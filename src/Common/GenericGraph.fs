// Copyright (c) 2019 - for information on the respective copyright owner
// see the NOTICE file and/or the repository 
// https://github.com/boschresearch/blech.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

module Blech.Common.GenericGraph
/// A Graph consists of nodes and edges.
/// The corresponding types are implemented in this module.
/// Node and Edge are both parameterised by 'NodeData and 'EdgeData. These are
/// the types of the contents that a node or edge can carry. 
///
/// The graph is implemented using mutable (references to) data. This allows
/// in-place updates as we know it from OO programming. However all of this
/// should be hidden from the user of this module.
/// Basic methods are provided to
///     - create / delete nodes and edges

open System.Collections.Generic

// this is used to generate unique IDs for nodes
let mutable private _counter = 0
let private getFreshNodeId () =
    _counter <- _counter+1
    _counter

   
/// A node carries a payload of type 'NodeData, has a unique ID and 
/// maintains two lists of edges: the ones leaving this node and the ones
/// pointing to this node from other nodes (hence we can traverse this 
/// directed graph backwards, if needed)
[<ReferenceEquality>] // super crucial annotation, otherwise comparisons are deep-value which results in stackoverflow on the cyclic data structures we have!!!
type Node<'NodeData, 'EdgeData when 'NodeData: equality and 'EdgeData: equality> = 
    {
        Payload : 'NodeData
        ID : int // needed for printing as dot graph to identify the nodes
        Outgoing : HashSet<Edge<'NodeData, 'EdgeData>> // mutable
        Incoming : HashSet<Edge<'NodeData, 'EdgeData>> // mutable
    }
with
    /// Add an edge to the list of edges that leave this node
    member this.AddOutgoing edge =
        this.Outgoing.Add edge |> ignore
    
    /// Add an edge to the list of edges that point to this node from other nodes
    member this.AddIncoming edge =
        this.Incoming.Add edge |> ignore

    /// Remove the given edge from the list of edges that point to this from other nodes
    member this.DeleteIncomingEdge edge =
        this.Incoming.Remove edge |> ignore

    /// Remove the given edge from the list of edge that point from this to other nodes
    member this.DeleteOutgoingEdge edge =
        this.Outgoing.Remove edge |> ignore

    member this.Successors =
        seq { for edge in this.Outgoing do yield edge.Target }

    member this.Predecessors =
        seq { for edge in this.Incoming do yield edge.Source }
    
    /// Generate a string representation for this node (to be used in DOT)
    override this.ToString() =
        let idstr = this.ID.ToString()
        let payloadStr = this.Payload.ToString()
        sprintf "\"%s\" %s\n" idstr payloadStr
        //"\"" + this.ID.ToString() + "\" " + this.Payload.ToString() + "\n"
    
    /// Factory for creating new nodes without any edges
    static member Create (p:'NodeData) =
        {
            Payload = p
            ID = getFreshNodeId()
            Outgoing = HashSet()
            Incoming = HashSet()
        }
    
    
/// An edge carries a payload of type 'EdgeData and knows its source and
/// target. 
and Edge<'NodeData, 'EdgeData when 'NodeData: equality and 'EdgeData: equality> = 
    {
        Payload : 'EdgeData
        Source : Node<'NodeData, 'EdgeData>
        Target : Node<'NodeData, 'EdgeData>
    }
with
    /// Generate a string representation of this edge (to be used in DOT)
    override this.ToString () =
        let sourceStr = this.Source.ID.ToString()
        let targetStr = this.Target.ID.ToString()
        let payloadStr = this.Payload.ToString()
        sprintf "\"%s\" -> \"%s\"%s\n" sourceStr targetStr payloadStr
        //"\"" + this.Source.ID.ToString() + "\" -> \"" + this.Target.ID.ToString() + "\"" + this.Payload.ToString() + "\n"
    
    /// Factory, creates a new edge and adds it to the respective lists
    /// Gotos for source and ComeFroms for target.
    static member Create (p:'EdgeData) source target =
        let result = {
            Payload = p
            Source = source
            Target = target
        }
        source.AddOutgoing result
        target.AddIncoming result
        result
    
and [<StructuredFormatDisplay("{PrintObjectAsString}")>] 
Graph<'NodeData, 'EdgeData when 'NodeData: equality and 'EdgeData: equality> =
    {
        Nodes : HashSet<Node<'NodeData, 'EdgeData>> // mutable
        Edges : HashSet<Edge<'NodeData, 'EdgeData>> // mutable
    }
with
    /// Add a new node without any edges to the graph
    member this.AddNode (p:'NodeData) =
        let newNode = Node<'NodeData, 'EdgeData>.Create p
        this.Nodes.Add newNode
        |> ignore
        newNode
        
    /// Add a new edge to the graph that connects source with target
    member this.AddEdge (p:'EdgeData) source target =
        Edge<'NodeData, 'EdgeData>.Create p source target
        |> this.Edges.Add
        |> ignore
        
    /// Remove node from the graph and all edges to and from it
    member this.RemoveNode (node: Node<'NodeData, 'EdgeData>) =
        // copies required because iterating over original sequences 
        // directly and deleting at the same time leads to runtime error
        let incoming = Seq.toArray node.Incoming
        let outgoing = Seq.toArray node.Outgoing
        incoming |> Array.iter (fun e -> (this.RemoveEdge e))
        outgoing |> Array.iter (fun e -> (this.RemoveEdge e))
        this.Nodes.Remove node
        |> ignore

    /// Remove edge from the graph (and update source and target nodes accordingly)
    member this.RemoveEdge (edge: Edge<'NodeData, 'EdgeData>) =
        edge.Source.DeleteOutgoingEdge edge
        edge.Target.DeleteIncomingEdge edge
        this.Edges.Remove edge
        |> ignore

    /// Replace the oldNode by newNode, meaning that
    /// - for every edge that points to oldNode a new edge points to newNode
    /// - oldNode (and all adjacent edges) are deleted
    member this.ReplaceNodeBy oldNode newNode =
        let redirect edge =
            if edge.Source = oldNode then
                // self-loop
                this.AddEdge edge.Payload newNode newNode
            else
                // distinct node
                this.AddEdge edge.Payload edge.Source newNode

        let incoming = Seq.toArray oldNode.Incoming
        incoming |> Array.iter redirect
        this.RemoveNode oldNode

    /// Replace the payload of a specified node, which is done by
    /// creating a new node with the same transitions but new payload
    /// and deleting the old one
    member this.ReplacePayloadInBy oldNode newPayload = 
        // create new node with new payload
        let newNode = this.AddNode newPayload
        // copy all incoming and outgoing transitions to new node
        oldNode.Incoming |> Seq.iter (fun e -> this.AddEdge e.Payload e.Source newNode)
        oldNode.Outgoing |> Seq.iter (fun e -> this.AddEdge e.Payload newNode e.Target)
        // remove old node
        this.RemoveNode oldNode

    member this.FilterNodes criterion =
        this.Nodes |> Seq.filter (fun node -> criterion (node.Payload))

    member this.FilterEdges criterion =
        this.Edges |> Seq.filter (fun edge -> criterion (edge.Payload))

    member this.PrintObjectAsString = this.ToString()
    /// Generate a string representation of the graph (for use in DOT)
    override this.ToString () =
        let edges = 
            this.Edges
            |> Seq.map (fun e -> e.ToString())
            |> Seq.fold (+) "" //failsafe, as compared to reduce
        let nodes =
            this.Nodes
            |> Seq.map (fun n -> n.ToString())
            |> Seq.fold (+) ""

        "digraph TestGraph{\n {" + nodes + "}\n" + edges + "}"

    /// Returns an empty graph
    static member Empty () =
        {
            Nodes = HashSet()
            Edges = HashSet()
        }

    /// Shorthand for JoinAll [gr1; gr2]
    static member Join gr1 gr2 =
        Graph<'NodeData, 'EdgeData>.JoinAll [gr1; gr2]

    /// Returns a new graph that contains all nodes and edges of the given
    /// graph. Changes to the original nodes or edges will change the 
    /// corresponding nodes or edges in this new graph and vice versa.
    static member JoinAll grs =
        let newGraph = Graph<'NodeData, 'EdgeData>.Empty()
        match grs with
        | [] -> ()
        | others -> 
            others |> List.iter (fun g -> newGraph.Nodes.UnionWith g.Nodes)
            others |> List.iter (fun g -> newGraph.Edges.UnionWith g.Edges)
        newGraph

    // this is copy code from clone function below with minor modifications
    static member SubGraphFromNodes (nodes: Node<_,_> seq) = 
        let newGraph = Graph<_,_>.Empty()
        let nodeMapping = Dictionary()
        nodes
        |> Seq.iter (fun node -> 
            let newNode = (newGraph.AddNode node.Payload)
            nodeMapping.Add(node,newNode)
            |> ignore)
        nodes
        |> Seq.collect (fun n -> Seq.concat [n.Incoming; n.Outgoing])
        |> Seq.filter (fun e -> nodeMapping.ContainsKey e.Source && nodeMapping.ContainsKey e.Target)
        |> Seq.iter (fun edge -> newGraph.AddEdge edge.Payload nodeMapping.[edge.Source] nodeMapping.[edge.Target])
        nodeMapping,newGraph

    static member CycleFromNodes (nodes: Node<_,_> []) =
        let newGraph = Graph<_,_>.Empty()
        let nodeMapping = Dictionary()
        for node in nodes do
            let newNode = (newGraph.AddNode node.Payload)
            nodeMapping.Add(node, newNode)
        let rec traverse ns =
            match ns with
            | n1 :: n2 :: rest ->
                n1.Outgoing
                |> Seq.filter (fun e -> n2 = e.Target) // there should be precisely one such edge
                |> Seq.iter (fun edge -> newGraph.AddEdge edge.Payload nodeMapping.[edge.Source] nodeMapping.[edge.Target])
                traverse (n2 :: rest)
            | _ -> ()
        let nodeLst = 
            nodes.[nodes.Length-1] :: (List.ofArray nodes)
            |> List.rev 
        traverse nodeLst
        nodeMapping, newGraph

            
////////////// adapted from Blech.Core.Graph.fs ///////////////////////////////
    
/// This type is used to mark the vertices during a traversal
type private NodeLabel = Unvisited | Visited | Finished


///    Performs a depth-first-traversal of the graph.
///
/// forward - Boolean flag indicating whether traversal is going forward
///    or backward.
/// nodes - Sequence of nodes that the DFS will start from.
/// onNodeVisit - A callback which is called with a node as paramter when a node is
///    visited the first time. If the callback returns true, traversal
///    aborted and the whole call returns true, otherwise traversal is
///    proceed.
/// onNodeFinish - A callback which is called with a node as paramter when a node is
///    visited the last time (finished). If the callback returns true,
///    traversal aborted and the whole call returns true, otherwise
///    traversal is proceed.
/// onCycleDetect - A callback which is called with a node as paramter when a cycle is
///    found. If the callback returns true, traversal aborted and the whole
///    call returns true, otherwise traversal is proceed.
/// returns true if the traversal was aborted by a callback which returned true.
///    If the traversal was not aborted, it returns false.
let depthsFirstTraverse selectNeighbours nodes onNodeVisit onNodeFinish onCycleDetect onRevisit =
    
    // Keep track of visited nodes, default label is Unvisited
    let labelling = new Dictionary<_, NodeLabel> ()
    let labelOf node = try labelling.[node] with _ -> Unvisited
    let updateLabel node label =
        labelling.Remove node |> ignore
        labelling.Add (node, label)

    // recursive function to visit the nodes
    let rec dft pathSoFar (node: Node<_,_>) =
        updateLabel node Visited
            
        // stop, if one call returns true
        Seq.exists id (
            seq {
                yield onNodeVisit pathSoFar node
                let neighbours = selectNeighbours node
                    
                for neighbour in neighbours do
                    match labelOf neighbour with
                    | Unvisited -> yield (dft (node :: pathSoFar) neighbour)
                    | Visited   -> yield (onCycleDetect (node :: pathSoFar) neighbour)
                    | Finished  -> yield (onRevisit (node :: pathSoFar) neighbour)
                    
                updateLabel node Finished
                    
                yield onNodeFinish pathSoFar node
            }
        )
        
    // stop, if one call returns true
    Seq.exists id (
        seq {
            for node in nodes do
                if labelOf node = Unvisited
                then yield (dft [] node)
                else ()
        }
    )


///    Performs a depth-first-traversal of the graph along the forward
///    edges
/// nodes - Sequence of nodes that the DFS will start from.
/// onNodeVisit - A callback which is called with a node as paramter when a node is
///    visited the first time. If the callback returns true, traversal
///    aborted and the whole call returns true, otherwise traversal is
///    proceed.
/// onNodeFinish - A callback which is called with a node as paramter when a node is
///    visited the last time (finished). If the callback returns true,
///    traversal aborted and the whole call returns true, otherwise
///    traversal is proceed.
/// onCycleDetect - A callback which is called with a node as paramter when a cycle is
///    found. If the callback returns true, traversal aborted and the whole
///    call returns true, otherwise traversal is proceed.
/// returns true if the traversal was aborted by a callback which returned true.
///    If the traversal was not aborted, it returns false.
let depthsFirstForward nodes onNodeVisit onNodeFinish onCycleDetect onRevisit =
    let selectNeighbours (n: Node<_,_>) = n.Successors
    depthsFirstTraverse selectNeighbours nodes onNodeVisit onNodeFinish onCycleDetect onRevisit


///    Performs a depth-first-traversal of the graph along the backward
///    edges
/// nodes - Sequence of nodes that the DFS will start from.
/// onNodeVisit - A callback which is called with a node as paramter when a node is
///    visited the first time. If the callback returns true, traversal
///    aborted and the whole call returns true, otherwise traversal is
///    proceed.
/// onNodeFinish - A callback which is called with a node as paramter when a node is
///    visited the last time (finished). If the callback returns true,
///    traversal aborted and the whole call returns true, otherwise
///    traversal is proceed.
/// onCycleDetect - A callback which is called with a node as paramter when a cycle is
///    found. If the callback returns true, traversal aborted and the whole
///    call returns true, otherwise traversal is proceed.
/// returns true if the traversal was aborted by a callback which returned true.
///    If the traversal was not aborted, it returns false.
let private depthsFirstBackward nodes onNodeVisit onNodeFinish onCycleDetect onRevisit =
    let selectNeighbours (n: Node<_,_>) = n.Predecessors
    depthsFirstTraverse selectNeighbours nodes onNodeVisit onNodeFinish onCycleDetect onRevisit

/// Simple function which is used as callback
let proceed _ _ = false

/// The function returns true if the given graph has cycles, otherwise false
let hasCycles (graph : Graph<_, _>) =
    depthsFirstForward graph.Nodes proceed proceed (fun _ _ -> true) proceed

/// Determines a topological order of all vertices contained in the graph.
/// Returns a pair (hasCycle,list) where hasCycle is a Boolean flag whether the graph contains a cylce.
/// If the graph is cyclic, list contains the found cycle.
/// If the graph is acyclic, list contains a topological order.
let topologicalSort (graph : Graph<_, _>) =
    let list = new List<_> ()
    let hasCycle = depthsFirstBackward graph.Nodes proceed (fun _ l -> list.Add (l); false) (fun _ l -> list.Add (l); true) proceed
    (hasCycle, list)

/// return list of strongly connected components (given by sets of nodes)
let stronglyConnectedComponents (graph : Graph<_, _>) =
    // components and root of currently processed component
    let components = new Dictionary<_,_> ()
    let curRoot = ref None
    //let componentsOrder = new List<_> ()

    // first create a topological order if existing
    let mutable orderedVertices = []
    ignore <| depthsFirstForward graph.Nodes proceed (fun _ node -> orderedVertices <- (node::orderedVertices); false) proceed proceed

    // now find components by backward visit in that order
    let discover _ cur =
        if (!curRoot) = None then
            curRoot := Some cur 
            components.[cur] <- new HashSet<_> ()
        else
            ()
        components.[(!curRoot).Value].Add cur |> ignore
        false
    let finish _ cur =
        if (!curRoot) = Some cur then curRoot := None else ()
        //componentsOrder.Add cur
        false
    ignore <| depthsFirstBackward orderedVertices discover finish proceed proceed 
    //now components contains all SCCs
    // transform them to subgraphs
    components
    |> Seq.map (fun comp -> comp.Value)
/////////////// end of code copy //////////////////////////////////////////////

/// Find all paths from a node to another one without cycles
let allSimplePaths selectNeighbours source destination =
    let mutable pathsFound = []
    let checkDestination pathSoFar node =
        if node = destination then
            let path = node :: pathSoFar |> List.rev
            pathsFound <- path :: pathsFound
            false
        else false
    ignore <| depthsFirstTraverse selectNeighbours [source] checkDestination proceed proceed checkDestination
    pathsFound


        
/// Given an SCC decomposition of a graph, generate the component graph G_SCC from it
let generateGsccFromGraph payloadTransformer (decomposition:Dictionary<Node<_,_>,HashSet<_>>) =
    let gscc = Graph<_,_>.Empty()
    let mapping = Dictionary()
    // for every key create a node in G_SCC with payload being the set of nodes in the component
    decomposition.Keys
    |> Seq.iter (
        fun node ->
            let newNode = gscc.AddNode decomposition.[node]
            decomposition.[node]
            |> Seq.iter (fun x -> mapping.Add(x, newNode))
    )
    // for every edge between SCCs (seq or wr) add an edge in G_SCC if not yet there
    decomposition.Keys
    |> Seq.iter (
        fun representative ->
            let nodeSet = decomposition.[representative] // get a component
            nodeSet 
            |> Seq.map (fun n -> n.Outgoing) // get all transitions of all nodes in this component
            |> Seq.concat
            |> Seq.filter (fun edge -> if not (nodeSet.Contains edge.Target) then true else false) // from these select all transitions that leave this component
            |> Seq.iter (fun edge -> 
                let target = edge.Target
                let weight = payloadTransformer edge
                // if in G_SCC there is no edge from corresponding representative to representative of target then add it now
                let link = 
                    mapping.[representative].Outgoing
                    |> Seq.tryPick (fun e -> if e.Target = mapping.[target] then Some e else None) 
                match link with
                | None -> gscc.AddEdge weight mapping.[representative] mapping.[target]
                // if a seq edge with weight 0 is present but we found a wr edge with weight 1, replace it
                | Some e -> 
                    if e.Payload < weight then
                        gscc.RemoveEdge e
                        gscc.AddEdge weight mapping.[representative] mapping.[target]
            )
    )
    gscc

/// Create a deep copy of a given graph
let clone (graph : Graph<'a,'b>) = 
    let newGraph = Graph<'a,'b>.Empty()
    let nodeMapping = Dictionary()
    graph.Nodes
    |> Seq.iter (fun node -> 
        let newNode = (newGraph.AddNode node.Payload)
        nodeMapping.Add(node,newNode)
        |> ignore)
    graph.Edges
    |> Seq.iter (fun edge -> newGraph.AddEdge edge.Payload nodeMapping.[edge.Source] nodeMapping.[edge.Target])
    newGraph

    
let private stripDanglingEdges (nodes: HashSet<_>) =
    let removeFromIncoming = HashSet<Edge<_,_>>()
    let removeFromOutgoing = HashSet<Edge<_,_>>()
    for node in nodes do
        for edge in node.Incoming do
            if not (nodes.Contains edge.Source) then removeFromIncoming.Add edge |> ignore
        for edge in node.Outgoing do
            if not (nodes.Contains edge.Target) then removeFromOutgoing.Add edge |> ignore

    for edge in removeFromIncoming do
        edge.Target.Incoming.Remove edge |> ignore
    for edge in removeFromOutgoing do
        edge.Source.Outgoing.Remove edge |> ignore


let mergeMappings (m1:Dictionary<Node<_,_>,Node<_,_>>) (m2:Dictionary<Node<_,_>,Node<_,_>>) =
    let resultMapping = Dictionary<Node<_,_>,Node<_,_>>()
    for keyOfM2 in m2.Keys do
        for kvp in m1 do
            if kvp.Value = keyOfM2 then resultMapping.Add(kvp.Key, m2.[keyOfM2])
    resultMapping

// DBLP:journals/siamcomp/Johnson75
// https://www.cs.tufts.edu/comp/150GA/homeworks/hw1/Johnson%2075.PDF
// implemented as in the paper without adaptations
// to functional style or architectural changes
/// Find every cycle in a directed graph
/// ASSUMPTION no self-loops
let johnson75 graph =
    //let graph = clone graph // shadow the original and modify the clone only
    let mapping, graph = Graph<_,_>.SubGraphFromNodes graph.Nodes
    let blocked = HashSet<Node<_,_>>()
    let blockedMap = Dictionary<Node<_,_>, HashSet<Node<_,_>>>() // map a node to a set of blocked nodes. 
    let stack = Stack<Node<_,_>>()
    let cycles = ResizeArray<Dictionary<Node<_,_>,Node<_,_>> * Graph<_,_>>()
    let mutable startNode: Node<_,_> option = None
        
    let rec circuit node : bool =
            
        let rec unblock node : unit =
            ignore <| blocked.Remove node
            let pendingOnNode = if blockedMap.ContainsKey node then blockedMap.[node] else HashSet()
            while pendingOnNode.Count > 0 do
                let someNode = Seq.head pendingOnNode
                ignore <| pendingOnNode.Remove someNode
                if blocked.Contains someNode then
                    unblock someNode
            
        let mutable foundCycle = false
        stack.Push node
        ignore <| blocked.Add node
        for succ in node.Successors do
            if succ = startNode.Value then
                //output cycle
                let mapping2, cycle = Graph<_,_>.CycleFromNodes (stack.ToArray())
                ignore <| cycles.Add (mergeMappings mapping mapping2,cycle) // we add the mapping of original graph nodes to nodes of newly created graph so the calling algorithm may determine whether the cycle contains a specic node
                foundCycle <- true
            else
                if not (blocked.Contains succ) then
                    if circuit succ then
                        foundCycle <- true
        if foundCycle then unblock node
        else
            for succ in node.Successors do
                if not (blockedMap.ContainsKey succ) then blockedMap.Add (succ, HashSet())
                ignore <| blockedMap.[succ].Add node
        let popped = stack.Pop()
        assert (popped = node)
        foundCycle
        
    let rec magik g =
        if g.Nodes.Count > 0 then
            let nontrivialSCCs = 
                stronglyConnectedComponents g
                |> Seq.filter (fun scc -> scc.Count > 1)
            if not (Seq.isEmpty nontrivialSCCs) then
                let leastSCC = Seq.head nontrivialSCCs
                stripDanglingEdges leastSCC
                startNode <- Some <| Seq.head leastSCC
                //init
                for node in leastSCC do
                    ignore <| blocked.Remove node
                    if blockedMap.ContainsKey node then blockedMap.[node].Clear()
                ignore <| circuit startNode.Value
                g.RemoveNode startNode.Value
                magik g
        
    magik graph
            
        
    cycles