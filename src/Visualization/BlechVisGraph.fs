module Blech.Visualization.BlechVisGraph

    open Blech.Common
    open Blech.Common.GenericGraph
    open System.Collections.Generic
    open Blech.Frontend.CommonTypes

    /// Specifies a (input or output parameter). First String specifies the type of the Parameter, second String specifies the name.
    type Param = { TypeName: string; Name: string}

    /// Gives the xth element of a 4-tuple or triple.
    let frst3 (a,_,_)  = a
    let scnd3 (_,b,_)  = b
    let thrd3 (_,_,c)  = c
    let frst (a,_,_,_) = a
    let scnd (_,b,_,_) = b
    let thrd (_,_,c,_) = c  
    let frth (_,_,_,d) = d

    /// List of params. Might need some operations?                
    type ParamList = Param list

    /// Type for identifying sources or targets
    type SourceOrTarget = Source | Target
   
    /// Facadeing the complex expression, for short: Visgraph.
    type VisGraph = GenericGraph.Graph<NodePayload, EdgePayload>      

    /// Payload to enter in an activity graph.
    and ActivityPayload = {InputParams : ParamList; OutputParams : ParamList; LocalVars : string list}

    /// Payload to fill into a cobegin node.
    and CobeginPayload = (VisGraph * Strength) list

    /// Shows if activity payload is present
    and IsActivity = IsActivity of ActivityPayload | IsNotActivity

    /// Specifies a complex node to a specific abort type. The strings are the abort labels.
    and IsAbort = AbortWhen of string | AbortRepeat of string | Neither
    
    /// Content of a complex node.
    and ComplexNode = {Body : VisGraph; IsActivity : IsActivity; CaseClosingNode : Option<BlechNode>; IsAbort : IsAbort}
    
    /// Type to match whether a node is simple or complex or a cobegin node. Cobegin nodes are very different from others due to their concurrenc nature.
    /// IsActivityCall consists of the input and output variable names.
    and ComplexOrSimpleOrCobegin = IsComplex of ComplexNode | IsSimple | IsCobegin of CobeginPayload | IsActivityCall of (string list * string list)

    /// Determines if a node is an initial node.
    and IsInit = IsInit | IsNotInit

    /// Determines if a node is a final node.
    and IsFinal = IsFinal | IsNotFinal

    /// Determines whether something is "Initial" or "Final".
    and InitOrFinalOrNeither = {Init : IsInit; Final : IsFinal} with 
        member x.ToString = (match x.Init with IsInit -> "init" | IsNotInit -> "not init") + " " + (match x.Final with IsFinal -> "final" | IsNotFinal -> "not final")
  
    /// Determines if a node closes an if-else case.
    and StateCount = int

    /// Indicating, if a node has been transformed to sctx (visualized) or not.
    and WasVisualized = Visualized | NotVisualized

    /// Indicating, whether outgoing edges of this node have been edge optimized.
    and WasEdgeOptimized = Optimized | NotOptimized

    /// Indicating, whether a node has been hierarchy optimized (checked for hierarchy, and hierarchy flattened if so).
    and WasHierarchyOptimized = HierarchyOptimized | NotHierarchyOptimized

    /// Payload for a node.
    and NodePayload = { Label : string; 
                        IsComplex : ComplexOrSimpleOrCobegin ; 
                        IsInitOrFinal : InitOrFinalOrNeither; 
                        StateCount : StateCount;
                        mutable WasVisualized : WasVisualized;
                        mutable WasHierarchyOptimized: WasHierarchyOptimized} with
        member x.Visualize = x.WasVisualized <- Visualized
        member x.SetHierarchyOptimized = x.WasHierarchyOptimized <- HierarchyOptimized
        member x.SetFinalStatusOn = {Label = x.Label; IsComplex = x.IsComplex; IsInitOrFinal = {Init = x.IsInitOrFinal.Init; Final = IsFinal}; StateCount = x.StateCount; WasVisualized = NotVisualized; WasHierarchyOptimized = x.WasHierarchyOptimized}
        member x.SetFinalStatusOff = {Label = x.Label; IsComplex = x.IsComplex; IsInitOrFinal = {Init = x.IsInitOrFinal.Init; Final = IsNotFinal}; StateCount = x.StateCount; WasVisualized = NotVisualized; WasHierarchyOptimized = x.WasHierarchyOptimized}
        member x.SetInitStatusOn = {Label = x.Label; IsComplex = x.IsComplex; IsInitOrFinal = {Init = IsInit; Final = x.IsInitOrFinal.Final}; StateCount = x.StateCount; WasVisualized = NotVisualized; WasHierarchyOptimized = x.WasHierarchyOptimized}
        member x.SetInitStatusOff = {Label = x.Label; IsComplex = x.IsComplex; IsInitOrFinal = {Init = IsNotInit; Final = x.IsInitOrFinal.Final}; StateCount = x.StateCount; WasVisualized = NotVisualized; WasHierarchyOptimized = x.WasHierarchyOptimized}

    /// Determines what kind of edge the edge ist.
    and EdgeProperty = IsAwait | IsConditional | IsImmediate | IsTerminal | IsAbort | IsConditionalTerminal

    /// Payload for an edge.
    and EdgePayload = {Label : string; Property : EdgeProperty; mutable WasOptimized : WasEdgeOptimized} with
        member x.CopyAsOptimized = {Label = x.Label ; Property = x.Property; WasOptimized = Optimized}
        member x.CopyAsNotOptimized = {Label = x.Label ; Property = x.Property; WasOptimized = NotOptimized}
        member x.CopyWithPropertyImmediate = {Label = x.Label ; Property = IsImmediate; WasOptimized = x.WasOptimized}
        member x.CopyWithPropertyConditional = {Label = x.Label ; Property = IsConditional; WasOptimized = x.WasOptimized}

    /// Node of a graph extracted from Blech code.
    and BlechNode = Node<NodePayload, EdgePayload>

    /// Edge of a graph extracted from Blech code.
    and BlechEdge = Edge<NodePayload, EdgePayload>

    /// Type for an edge accumulator. Edge String * Recursive Node Strings.
    and EdgeAccumulator = string * string

    /// Type for sequentially constructing the graph. Consists of: current graph, previous available node for connection and current state count (for distinct state identifiers.)
    /// Fourth element is a list of strings that contains the names of all parameters needed to make function calls in this scope. 
    /// Fourth element is used to compare to the list of defined in- and output variables to determine the missing variables that have to be defined.
    /// Can later be used for implementation of actual local variables.
    and GraphBuilder = VisGraph * BlechNode * int * string list

    let NeitherInitOrFinal = {Init = IsNotInit; Final = IsNotFinal}
    let InitNotFinal = {Init = IsInit; Final = IsNotFinal}
    let FinalNotInit = {Init = IsNotInit; Final = IsFinal}
    let InitAndFinal = {Init = IsInit; Final = IsFinal}

    //____________________ Find first await on every path in a graph.____________________________
    /// TODO comment.
    let isValidNode (validNodeIdList : int list) = fun (n : BlechNode) -> List.contains n.Payload.StateCount validNodeIdList
    let isValidEdge (validNodeIdList : int list) = fun (e : BlechEdge) -> List.contains e.Target.Payload.StateCount validNodeIdList

    /// TODO comment.
    let rec findFirstAwaitNodeOnEveryPath (entryPoint : BlechNode) (validNodes : int list) : BlechNode list=
        List.distinct (findAwaitsOnNodeAndSubsequentPaths entryPoint validNodes)

    /// TODO comment.
    and private findAwaitsOnNodeAndSubsequentPaths (currentNode : BlechNode) (validNodes : int list) : BlechNode list=
        let isAwait = checkEdgesForAwait (List.filter (isValidEdge validNodes) (Seq.toList currentNode.Outgoing))
        let validSuccessors = List.filter (isValidNode validNodes) (Seq.toList currentNode.Successors)
        match isAwait with
            | true -> currentNode :: addAllSubsequentNodes validSuccessors validNodes
                      // Found first await, just add all subsequent nodes to the list.
            | false -> checkNodesForAwaitsInPath validSuccessors validNodes
    
    /// TODO comment.
    and private checkNodesForAwaitsInPath (nodes : BlechNode list) (validNodes : int list) : BlechNode list =
        match nodes with
            | head :: tail -> (findFirstAwaitNodeOnEveryPath head validNodes) @ (checkNodesForAwaitsInPath tail validNodes)
            | [] -> []

    /// TODO comment.
    and private checkEdgesForAwait (edges: BlechEdge list) : bool =
        match edges with
            | head :: tail -> match head.Payload.Property with
                                | IsAwait -> true
                                | _ -> checkEdgesForAwait tail
            | [] -> false

    /// TODO comment.
    /// No filtering of nodes needed, given nodes are already valid nodes.
    and private addAllSubsequentNodes (nodes : BlechNode list) (validNodes: int list) : BlechNode list = 
        match nodes with
            | head :: tail -> let validSuccessors = List.filter (isValidNode validNodes) (Seq.toList head.Successors)
                              head :: (addAllSubsequentNodes validSuccessors validNodes) @ (addAllSubsequentNodes tail validNodes)
            | [] -> []

    //____________________________________Find specific nodes/edges in hashset/list.
    /// Finds the node that has matches true on the given function and returns it.
    let private findNodeInHashSet(nodes : HashSet<BlechNode>) (fnct : BlechNode -> bool): BlechNode =
            nodes 
            |> Seq.toList 
            |> List.tryFind fnct 
            |> (fun option -> match option.IsSome with true -> option.Value | false -> failwith("No node with the specified properties found in this graph."))

    /// Finds the node that has Property Init set to true and returns it.
    let findInitNodeInHashSet(nodes : HashSet<BlechNode>) : BlechNode =
            findNodeInHashSet nodes (fun node -> match node.Payload.IsInitOrFinal.Init with IsInit -> true | _ -> false)
    
    /// Finds the node that has Property Init set to true and returns it.
    let findFinalNodeInHashSet(nodes : HashSet<BlechNode>) : BlechNode =
            findNodeInHashSet nodes (fun node -> match node.Payload.IsInitOrFinal.Final with IsFinal -> true | _ -> false)

    /// Determines if apart of this edge, another edge between source and target is present.
    /// Edge list should, as peer previous conditions in the code be a list of two. Asserting this fact nonetheless.
    let immediateAndAbortNode (edge : BlechEdge) (edges : BlechEdge list) : bool =
        if (not (List.contains edge edges)) then failwith "Expected given edge to be part of given list. Was not the case."

        // Now check if both edges have same source and target.
        let counter = 
            fun (tuple: int * BlechEdge list) (e:BlechEdge) -> 
                if e.Source.Payload.StateCount = edge.Source.Payload.StateCount && 
                    e.Source.Payload.StateCount = edge.Source.Payload.StateCount then 
                    (fst tuple + 1, e :: (snd tuple))
                else 
                    (fst tuple, snd tuple)
        let count = List.fold counter (0, []) edges
        let detectedEdges = snd count
        let countAbort = List.fold (fun (acc:int) (e:BlechEdge) -> match e.Payload.Property with IsAbort -> acc + 1 | _ -> acc) 0 detectedEdges
        let countImmediate = List.fold (fun (acc:int) (e:BlechEdge) -> match e.Payload.Property with IsImmediate -> acc + 1 | _ -> acc) 0 detectedEdges
        
        // We want exactly two edges between source and target. One abort and one immediate, others are unknown and unconsidered cases.
        (fst count) = 2 && countAbort = 1 && countImmediate = 1
        

    //____________________________________Remove element in list.
    /// Removes element from a list. If element is not in list, original list will be returned.
    let rec removeItem (item : 'T) (list : 'T list) =
        match item, list with
            | item, head :: tail -> if(item = head) then removeItem item tail else head :: removeItem item tail
            | _, [] -> []

    //_________________________________Add graph to graph in single not failable steps.
    /// Adds a given graph to a graph by imitating the nodes and replicating the edges (creating brand new objects that is).
    let rec addGraphToGraph (graph : VisGraph) (graphToAdd : VisGraph) : VisGraph = 
        // 1. Add all nodes from the graph with their respectve payloads.
        graphToAdd.Nodes |> Seq.iter (fun n -> graph.AddNode n.Payload |> ignore)        
        // 2. Imitate edges as given, for this find the corresponding now existing nodes from step 1 and add a new edge with these nodes and the given edge data.
        graphToAdd.Edges |> Seq.iter(fun e -> graph.AddEdge e.Payload (findNodeByStateCount e.Source.Payload.StateCount graph) (findNodeByStateCount e.Target.Payload.StateCount graph))
        graph

    /// Finds a specific Blechnode in a given list of nodes, specified by the StateCount of the desired node.
    and findNodeByStateCount (desiredCount: int) (graph: VisGraph) : BlechNode =
        graph.Nodes |> Seq.find (fun n -> n.Payload.StateCount = desiredCount)

   /////////////////// DEBUG ______________________
    let rec listNodes (nodes : BlechNode list) =
        match nodes with 
            | head :: tail ->   printfn "node s%i, outgoing size s%i, incoming size %i" head.Payload.StateCount (Seq.toList head.Outgoing).Length (Seq.toList head.Incoming).Length
                                listNodes tail
            | [] -> printf ""

    let rec listEdges (edges : BlechEdge list) =
        match edges with 
            | head :: tail ->   printfn "edge from s%i to s%i" head.Source.Payload.StateCount head.Target.Payload.StateCount
                                listEdges tail
            | [] -> printf ""