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

    /// Determines whether something is "Initial" or "Final".
    and InitOrFinalOrNeither = Init | Final | Neither

    /// Determines if a node closes an if-else case.
    and StateCount = int

    /// Indicating, if a node has been transformed to sctx (visualized) or not.
    and WasVisualized = Visualized | NotVisualized

    /// Payload for a node.
    and NodePayload = {Label : string; IsComplex : ComplexOrSimpleOrCobegin ; IsInitOrFinal : InitOrFinalOrNeither; StateCount : StateCount; mutable WasVisualized : WasVisualized} with
        member x.Visualize = x.WasVisualized <- Visualized
        member x.CopyWithInitOrFinalStatusSetTo (newStatus : InitOrFinalOrNeither) = {Label = x.Label; IsComplex = x.IsComplex; IsInitOrFinal = newStatus ; StateCount = x.StateCount; WasVisualized = NotVisualized}

    /// Determines what kind of edge the edge ist.
    and EdgeProperty = IsAwait | IsConditional | IsImmediate | IsTerminal | IsAbort

    /// Payload for an edge.
    and EdgePayload = {Label : string; Property : EdgeProperty} with
        member x.CopyWithPropertyImmediate = {Label = x.Label ; Property = IsImmediate}

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

    //____________________ Find first await on every path in a graph.____________________________
    /// TODO comment.
    let rec findFirstAwaitNodeOnEveryPath (entryPoint : BlechNode) : BlechNode list=
        List.distinct (findAwaitsOnNodeAndSubsequentPaths entryPoint)

    /// TODO comment.
    and private findAwaitsOnNodeAndSubsequentPaths (currentNode : BlechNode) : BlechNode list=
        let isAwait = checkEdgesForAwait (Seq.toList currentNode.Outgoing)
        match isAwait with
            | true -> [currentNode] @ addAllSubsequentNodes (Seq.toList currentNode.Successors) // Found first await, just add all subsequent nodes to the list.
            | false -> checkNodesForAwaitsInPath (Seq.toList currentNode.Successors)
    
    /// TODO comment.
    and private checkNodesForAwaitsInPath (nodes : BlechNode list) : BlechNode list =
        match nodes with
            | head :: tail -> (findFirstAwaitNodeOnEveryPath head) @ (checkNodesForAwaitsInPath tail)
            | [] -> []

    /// TODO comment.
    and private checkEdgesForAwait (edges: BlechEdge list) : bool =
        match edges with
            | head :: tail -> match head.Payload.Property with
                                | IsAwait -> true
                                | _ -> checkEdgesForAwait tail
            | [] -> false

    /// TODO comment.
    and private addAllSubsequentNodes (nodes : BlechNode list) : BlechNode list = 
        match nodes with
            | head :: tail -> [head] @ addAllSubsequentNodes (Seq.toList head.Successors) @ addAllSubsequentNodes tail
            | [] -> []

    //____________________________________Find specific nodes in hashset.
    /// Finds the node that has matches true on the given function and returns it.
    let private findNodeInHashSet(nodes : HashSet<BlechNode>) (fnct : BlechNode -> bool): BlechNode =
            nodes 
            |> Seq.toList 
            |> List.tryFind fnct 
            |> (fun option -> match option.IsSome with true -> option.Value | false -> failwith("No node with the specified properties found in this graph."))

    /// Finds the node that has Property Init set to true and returns it.
    let findInitNodeInHashSet(nodes : HashSet<BlechNode>) : BlechNode =
            findNodeInHashSet nodes (fun node -> match node.Payload.IsInitOrFinal with Init -> true | _ -> false)
    
    /// Finds the node that has Property Init set to true and returns it.
    let findFinalNodeInHashSet(nodes : HashSet<BlechNode>) : BlechNode =
            findNodeInHashSet nodes (fun node -> match node.Payload.IsInitOrFinal with Final -> true | _ -> false) 

///////////////////// FOR DEBUG
    let rec compareGraphToString (cmpstring1 : string) (cmpString: string) : bool =        
        cmpstring1.Equals cmpString

    and listGraph (graph : BlechNode list) : string =
        match graph with
                | head :: tail -> match head.Payload.IsComplex with IsComplex _ -> listActNodeAndSubgraphs head + listGraph tail | _ -> listGraph tail
                | [] -> ""

    and listActNodeAndSubgraphs(node : BlechNode) : string =
        let str = match node.Payload.IsComplex with 
                        | IsComplex a ->        //printfn "Complex state s%i" node.Payload.StateCount
                                                listEdges (Seq.toList node.Outgoing) + listGraph (Seq.toList a.Body.Nodes)
                        | _ -> //printf "State s%i " node.Payload.StateCount
                               listEdges (Seq.toList node.Outgoing)
        str

    and listEdges (edges : BlechEdge list) : string =
        match edges with
                | head :: tail -> (string head.Source.Payload.StateCount) + (string head.Target.Payload.StateCount) + listEdges tail
                | [] -> ""

   