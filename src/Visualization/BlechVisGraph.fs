module Blech.Visualization.BlechVisGraph

    open Blech.Common
    open Blech.Common.GenericGraph
    open System.Collections.Generic
    open Blech.Frontend.CommonTypes

    //____________________ Types.____________________________
    /// Specifies a (input or output parameter). First String specifies the type of the Parameter, second String specifies the name.
    type Param = { TypeName: string; Name: string}

    /// List of params. Might need some operations?                
    type ParamList = Param list

    /// Type for identifying sources or targets
    type SourceOrTarget = Source | Target
   
    /// Facadeing the complex expression, for short: Visgraph.
    type VisGraph = GenericGraph.Graph<NodePayload, EdgePayload>      

    /// Payload to enter in an activity graph.
    and ActivityPayload = {InputParams : ParamList; OutputParams : ParamList; LocalVars : string list}

    /// Determines if a node closes an if-else case.
    and StateCount = int

    /// Pair of ids: State Count and Secondary Id.
    and IdPair = StateCount * StateCount

    /// Optional id pair. Used for potential follow up nodes that need to be saved and identified.
    and IdPairOpt = {Opt :Option<IdPair>} with
        member x.UpdateSecondary i = if x.Opt.IsSome then {Opt = Some ((fst x.Opt.Value), i)} else {Opt = None}
        member x.StateCount = (fst x.Opt.Value)
        member x.SecondaryId = (snd x.Opt.Value)

    /// Payload to fill into a cobegin node. 
    and CobeginPayload = {Content : (VisGraph * Strength) list; CaseClosingNode : IdPairOpt} with
        member x.SetSecondaryIdOfCaseClosingNode i = {Content = x.Content; CaseClosingNode = x.CaseClosingNode.UpdateSecondary i}

    /// Shows if activity payload is present
    and IsActivity = IsActivity of ActivityPayload | IsNotActivity

    /// Run statement, calling an activity. In- and output variables.
    and IsActivityCall = (string list * string list)

    /// Specifies a complex node to a specific abort type. The strings are the abort labels.
    and IsAbort = AbortWhen of string | AbortRepeat of string | Neither
   
    /// Content of a complex node.
    and ComplexNode = {Body : VisGraph; IsActivity : IsActivity; CaseClosingNode : IdPairOpt; IsAbort : IsAbort} with
        member x.SetSecondaryIdOfCaseClosingNode i = 
            {Body = x.Body; IsActivity = x.IsActivity; CaseClosingNode = x.CaseClosingNode.UpdateSecondary i;IsAbort = x.IsAbort}
    
    /// Type to match whether a node is simple or complex or a cobegin node. Cobegin nodes are very different from others due to their concurrenc nature.
    /// IsActivityCall consists of the input and output variable names.
    and ComplexOrSimpleOrCobegin = IsComplex of ComplexNode | IsSimple | IsCobegin of CobeginPayload | IsActivityCall of IsActivityCall with
        member x.SetSecondaryIdOfCaseClosingNode i = 
            match x with 
                | IsComplex cmplx -> IsComplex (cmplx.SetSecondaryIdOfCaseClosingNode i)
                | IsCobegin cbgn-> IsCobegin (cbgn.SetSecondaryIdOfCaseClosingNode i)
                | _ -> x

    /// Determines if a node is an initial node.
    and IsInit = IsInit | IsNotInit

    /// Determines if a node is a final node.
    and IsFinal = IsFinal | IsNotFinal

    /// Determines whether something is "Initial" or "Final".
    and InitOrFinalOrNeither = {Init : IsInit; Final : IsFinal} with 
        member x.ToString = (match x.Init with IsInit -> "init" | IsNotInit -> "not init") + " " + (match x.Final with IsFinal -> "final" | IsNotFinal -> "not final")
        member x.IsFinalBool = match x.Final with IsFinal -> true | IsNotFinal -> false

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
                        SecondaryId : StateCount;
                        mutable WasVisualized : WasVisualized;
                        mutable WasHierarchyOptimized: WasHierarchyOptimized} with
        member x.SetSecondaryId i = {Label = x.Label; IsComplex = x.IsComplex.SetSecondaryIdOfCaseClosingNode i; IsInitOrFinal = x.IsInitOrFinal; StateCount = x.StateCount; SecondaryId = i; WasVisualized = NotVisualized; WasHierarchyOptimized = x.WasHierarchyOptimized}
        member x.Visualize = x.WasVisualized <- Visualized
        member x.SetHierarchyOptimized = x.WasHierarchyOptimized <- HierarchyOptimized
        member x.SetFinalStatusOn = {Label = x.Label; IsComplex = x.IsComplex; IsInitOrFinal = {Init = x.IsInitOrFinal.Init; Final = IsFinal}; StateCount = x.StateCount; SecondaryId = x.SecondaryId; WasVisualized = NotVisualized; WasHierarchyOptimized = x.WasHierarchyOptimized}
        member x.SetFinalStatusOff = {Label = x.Label; IsComplex = x.IsComplex; IsInitOrFinal = {Init = x.IsInitOrFinal.Init; Final = IsNotFinal}; StateCount = x.StateCount; SecondaryId = x.SecondaryId; WasVisualized = NotVisualized; WasHierarchyOptimized = x.WasHierarchyOptimized}
        member x.SetInitStatusOn = {Label = x.Label; IsComplex = x.IsComplex; IsInitOrFinal = {Init = IsInit; Final = x.IsInitOrFinal.Final}; StateCount = x.StateCount; SecondaryId = x.SecondaryId; WasVisualized = NotVisualized; WasHierarchyOptimized = x.WasHierarchyOptimized}
        member x.SetInitStatusOff = {Label = x.Label; IsComplex = x.IsComplex; IsInitOrFinal = {Init = IsNotInit; Final = x.IsInitOrFinal.Final}; StateCount = x.StateCount; SecondaryId = x.SecondaryId; WasVisualized = NotVisualized; WasHierarchyOptimized = x.WasHierarchyOptimized}

    /// Determines what kind of edge the edge ist.
    and EdgeProperty = IsAwait | IsConditional | IsImmediate | IsTerminal | IsAbort | IsConditionalTerminal

    /// Payload for an edge.
    and EdgePayload = {Label : string; Property : EdgeProperty; mutable WasOptimized : WasEdgeOptimized} with
        member x.CopyAsOptimized = {Label = x.Label ; Property = x.Property; WasOptimized = Optimized}
        member x.CopyAsNotOptimized = {Label = x.Label ; Property = x.Property; WasOptimized = NotOptimized}
        member x.CopyWithPropertyImmediate = {Label = x.Label ; Property = IsImmediate; WasOptimized = x.WasOptimized}
        member x.CopyWithPropertyTerminal =  {Label = x.Label ; Property = IsTerminal; WasOptimized = x.WasOptimized}
        member x.CopyWithPropertyConditional = {Label = x.Label ; Property = IsConditional; WasOptimized = x.WasOptimized}
        member x.CopyWithPropertyConditionalTerminal = {Label = x.Label ; Property = IsConditionalTerminal; WasOptimized = x.WasOptimized}

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
    and GraphBuilder = VisGraph * (Option<BlechNode>) * int * string list

    let NeitherInitOrFinal = {Init = IsNotInit; Final = IsNotFinal}
    let InitNotFinal = {Init = IsInit; Final = IsNotFinal}
    let FinalNotInit = {Init = IsNotInit; Final = IsFinal}
    let InitAndFinal = {Init = IsInit; Final = IsFinal}

    //____________________ Unspecified helping methods.____________________________
    /// Gives the xth element of a 4-tuple or triple.
    let frst3 (a,_,_)  = a
    let scnd3 (_,b,_)  = b
    let thrd3 (_,_,c)  = c
    let frst (a,_,_,_) = a
    let scnd (_,b,_,_) = b
    let thrd (_,_,c,_) = c  
    let frth (_,_,_,d) = d

    /// Returns the ids as a pair for a Blech node.
    let findIds = (fun (n:BlechNode) -> (n.Payload.StateCount, n.Payload.SecondaryId))

    /// Converts an edge to a int representation needed for the variable 'optimizedEdges'.
    let convertToIdTuple (e : BlechEdge) = ((e.Source.Payload.StateCount, e.Source.Payload.SecondaryId), 
                                            (e.Target.Payload.StateCount, e.Target.Payload.SecondaryId))

    /// Matches two given nodes by their id.
    let matchNodes = fun (n1 : BlechNode) (n2:BlechNode) -> n1.Payload.StateCount = n2.Payload.StateCount && n1.Payload.SecondaryId = n2.Payload.SecondaryId

    //____________________ Find first await on every path in a graph.____________________________
    /// Function that determines whether a node (identified by its state count) is valid, because it is part of a list of valid ids.
    let isValidNode (validNodeIdList : (int*int) list) = fun (n : BlechNode) -> List.contains (n.Payload.StateCount, n.Payload.SecondaryId) validNodeIdList
    /// Function that determines whether an edge (identified by state count of source and edge) is valid, because it is part of a list of valid ids.
    let isValidTarget (validNodeIdList : (int*int) list) = fun (e : BlechEdge) -> List.contains (e.Target.Payload.StateCount, e.Target.Payload.SecondaryId) validNodeIdList

    /// Starts the search of the first await on a path, given by a node starting the path. 
    /// The nodes that are allowed to be in the path are given by the list of state count integers.
    /// Successors of the nodes and its successors might be invalid and should not be considered, hence the list.
    /// Returns all valid nodes in the path that follow the first found await statement. Second element is the actual first awaiting node. Third element is the already checked nodes so far.
    /// If there is an await edge going out of the current node, we reached the first await.
    /// If the current node is an activity (call), it must contain an await, and is thus the first await statement.
    /// Hierarchies are broken from the inside out. Hence, if a complex is met, it is expected to have an await in it.
    let rec findFirstAwaitNodeOnEveryPath (entryPoint : BlechNode) 
                                          (validNodes : (StateCount * StateCount) list)
                                          (checkedNodes : (StateCount * StateCount) list)
                                          : BlechNode list * Option<BlechNode> *  (StateCount * StateCount) list =
        let isActivityCallOrOtherComplex = match entryPoint.Payload.IsComplex with
                                            | IsSimple _ -> false
                                            | _ -> true
        let isAwaitEdge = checkEdgesForAwait (List.filter (isValidTarget validNodes) (Seq.toList entryPoint.Outgoing))

        let validAndNotYetChecked = fun n -> isValidNode validNodes n && not (isValidNode checkedNodes n)
        let validSuccessors = List.filter (validAndNotYetChecked) (Seq.toList entryPoint.Successors)

        let listAndChecked = match isAwaitEdge || isActivityCallOrOtherComplex with
                                | true -> (addAllSubsequentNodes validSuccessors validNodes [entryPoint], Some entryPoint, checkedNodes)
                                // Found first await, just add all subsequent nodes to the list.
                                | false -> checkNodesForAwaitsInPath validSuccessors validNodes checkedNodes
        let distinctAndFilteredListOfValidNodes = if (scnd3 listAndChecked).IsSome then
                                                        List.filter (fun n -> not (matchNodes n (scnd3 listAndChecked).Value)) (List.distinct (frst3 listAndChecked))
                                                   else 
                                                        (List.distinct (frst3 listAndChecked))
        (distinctAndFilteredListOfValidNodes, scnd3 listAndChecked, thrd3 listAndChecked) 
    
    /// Recursively checks single nodes in a list of nodes for their first await.
    /// Returns: valid nodes after first await, first await node, and all checked nodes so far.
    and private checkNodesForAwaitsInPath (nodes : BlechNode list) 
                                          (validNodes : (int*int) list)
                                          (checkedNodes : (StateCount * StateCount) list)
                                          : BlechNode list * Option<BlechNode> *  (StateCount * StateCount) list =
        match nodes with
            | head :: tail -> let headChecked = findFirstAwaitNodeOnEveryPath head validNodes (findIds head::checkedNodes)
                              let tailChecked = checkNodesForAwaitsInPath tail validNodes (thrd3 headChecked)
                              let firstAwait = if (scnd3 headChecked).IsSome then scnd3 headChecked elif (scnd3 tailChecked).IsSome then scnd3 tailChecked else None
                              ((frst3 headChecked) @ (frst3 tailChecked), firstAwait, thrd3 tailChecked)
            | [] -> ([], None ,checkedNodes)

    /// Checks a list of edges, whether or not there is an await edges among them.
    and private checkEdgesForAwait (edges: BlechEdge list) : bool =
        match edges with
            | head :: tail -> match head.Payload.Property with
                                | IsAwait -> true
                                | _ -> checkEdgesForAwait tail
            | [] -> false

    /// Constructs a list of the given nodes and all subsequent nodes (that are valid).
    /// Valid nodes are ones that were in the subgraph and have not been checked yet.
    /// Nodes to check do not need to be filtered, as they have already been checked beforehand.
    /// The accumulator accumulates the subsequent nodes.
    and private addAllSubsequentNodes (nodesToCheck : BlechNode list) (validNodes: (int*int) list) (accumulator : BlechNode list): BlechNode list = 
        match nodesToCheck with
            | head :: tail -> let validnessCheck = fun node -> isValidNode validNodes node && not (isValidNode (List.map findIds accumulator) node)
                              let validSuccessors = List.filter validnessCheck (Seq.toList head.Successors)
                              //printfn "s%i%i, length vs %i, length valid nodes %i, length acc %i" head.Payload.StateCount head.Payload.SecondaryId validSuccessors.Length validNodes.Length accumulator.Length
                              //List.map (fun (s:BlechNode) -> printfn "s%s%s" (string s.Payload.StateCount) (string s.Payload.SecondaryId)) accumulator |> ignore
                              addAllSubsequentNodes (validSuccessors@tail) validNodes (head:: accumulator)
            | [] ->  accumulator

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

    /// Determines if there is a final node in a set of nodes.
    let isThereFinalNodeInHashSet(nodes : HashSet<BlechNode>) : bool =
         nodes 
         |> Seq.toList 
         |> List.tryFind (fun node -> match node.Payload.IsInitOrFinal.Final with IsFinal -> true | _ -> false) 
         |> (fun option -> option.IsSome)
    
    /// Checks a cobegin body for the presence of a final node in any of the regions.
    let rec isThereFinalNodeInCobegin (cbgnBody :(VisGraph * Strength) list) : bool = 
        match cbgnBody with
            | head :: tail -> if isThereFinalNodeInHashSet (fst head).Nodes then
                                true
                              else 
                                isThereFinalNodeInCobegin tail
            | [] -> false
    
    /// Determines if there is a final node in a set of nodes and returns its ids.
    let stateCountAndSecondaryOfFinalNodeIfPresent (nodes : HashSet<BlechNode>) : Option<int * int> =
         nodes 
         |> Seq.toList 
         |> List.tryFind (fun node -> match node.Payload.IsInitOrFinal.Final with IsFinal -> true | _ -> false) 
         |> (fun option -> 
                match option.IsSome with true -> Some (option.Value.Payload.StateCount, option.Value.Payload.SecondaryId) | _ -> None)

    /// Determines if apart of this edge, another edge between source and target is present.
    /// Edge list should, as peer previous conditions in the code be a list of two. Asserting this fact nonetheless.
    /// One edge should be an abort edge, the other one of the specified property.
    let specifiedAndAbortEdge (property : EdgeProperty) (edge : BlechEdge) (edges : BlechEdge list) : bool =
        if (not (List.contains edge edges)) then failwith "Expected given edge to be part of given list. Was not the case."

        // Now check if both edges have same source and target.
        let counter = 
            fun (tuple: int * BlechEdge list) (e:BlechEdge) -> 
                if matchNodes e.Source edge.Source && matchNodes e.Target edge.Target then 
                    (fst tuple + 1, e :: (snd tuple))
                else 
                    (fst tuple, snd tuple)
        let count = List.fold counter (0, []) edges
        let detectedEdges = snd count
        let countAbort = List.fold (fun (acc:int) (e:BlechEdge) -> match e.Payload.Property with IsAbort -> acc + 1 | _ -> acc) 0 detectedEdges
        let countOther = List.fold (fun (acc:int) (e:BlechEdge) -> match e.Payload.Property = property with true -> acc + 1 | false -> acc) 0 detectedEdges
        
        // We want exactly two edges between source and target. One abort and one immediate, others are unknown and unconsidered cases.
        (fst count) = 2 && countAbort = 1 && countOther = 1

    /// Checks whether the source and target of the edge have only edges between then regarding outgoing and incoming. All the edges are immediates for true.
    let onlyImmediatesOrConditionals (edge : BlechEdge) : bool = 
        let source = edge.Source
        let target = edge.Target
        let sourceOutgoings = (Seq.toList source.Outgoing)
        let targetIncomings = (Seq.toList target.Incoming)
        //printfn "source out %i" sourceOutgoings.Length
        //printfn "target in %i" targetIncomings.Length
        let cond1 = sourceOutgoings.Length = targetIncomings.Length && sourceOutgoings.Length >= 2 && targetIncomings.Length >= 2
        let edgesEqualToEdge = 
            (fun acc (e:BlechEdge) -> acc && matchNodes e.Source source && matchNodes e.Target target)
        let edgeTerminalOrImmediate =
            (fun acc (e:BlechEdge) -> 
                acc && (e.Payload.Property = IsImmediate || e.Payload.Property = IsTerminal || e.Payload.Property = IsConditional || e.Payload.Property = IsConditionalTerminal))
        let cond2 = List.fold edgesEqualToEdge true sourceOutgoings && List.fold edgesEqualToEdge true targetIncomings
        let cond3 = List.fold edgeTerminalOrImmediate true sourceOutgoings && List.fold edgeTerminalOrImmediate true targetIncomings

        cond1 && cond2 && cond3

    /// Finds for a node that is calling an activity, whether said activity contains a final node.
    /// This is given by the list of pairs, pairing the acitvity names with the presence indicator.
    /// If node is activity call, and called activity has final node, return true, else false.
    let nodeIsActivityCallAndHasFinalNode (current: BlechNode) (pairs : (string*bool) list) : bool =
        match current.Payload.IsComplex with
            | IsActivityCall _->let pair = List.find (fun e -> current.Payload.Label = fst e) pairs
                                snd pair
            | _ -> false

    /// Finds for a node that is calling an activity, whether said activity contains a final node.
    /// This is given by the list of pairs, pairing the acitvity names with the presence indicator.
    /// If node is activity call, and called activity has NO final node, return true, else false.
    let nodeIsActivityCallAndHasNoFinalNode (current: BlechNode) (pairs : (string*bool) list) : bool =
        match current.Payload.IsComplex with
            | IsActivityCall _->let pair = List.find (fun e -> current.Payload.Label = fst e) pairs
                                //List.map (fun e -> printfn "%s %b" (fst e) (snd e)) pairs |> ignore
                                //printfn "snd pair notted %b" (not (snd pair))
                                not (snd pair)
            | _ -> false

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
        graphToAdd.Edges |> 
         Seq.iter (fun e -> graph.AddEdge e.Payload 
                                          (findNodeByStateCount e.Source.Payload.StateCount e.Source.Payload.SecondaryId graph) 
                                          (findNodeByStateCount e.Target.Payload.StateCount e.Target.Payload.SecondaryId graph))
        graph

    /// Finds a specific Blechnode in a given list of nodes, specified by the StateCount of the desired node and the secondary identifier.
    and findNodeByStateCount (desiredCount: int) (desiredSecondary : int) (graph: VisGraph) : BlechNode =
        graph.Nodes |> Seq.find (fun n -> n.Payload.StateCount = desiredCount && n.Payload.SecondaryId = desiredSecondary)

   /////////////////// DEBUG ______________________
    let rec listNodes (nodes : BlechNode list) =
        match nodes with 
            | head :: tail ->   printfn "node s%i, second %i" head.Payload.StateCount head.Payload.SecondaryId
                                listNodes tail
            | [] -> printf ""

    let rec listEdges (edges : BlechEdge list) =
        match edges with 
            | head :: tail ->   printfn "edge from s%i%i to s%i%i" head.Source.Payload.StateCount head.Source.Payload.SecondaryId head.Target.Payload.StateCount head.Target.Payload.SecondaryId
                                listEdges tail
            | [] -> printf ""