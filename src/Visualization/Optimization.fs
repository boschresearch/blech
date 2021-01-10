 module Blech.Visualization.Optimization

    open Blech.Common.GenericGraph
    open Blech.Visualization.BlechVisGraph
    open Blech.Visualization.SctxGenerator

    /// Optimizes the nodes and their contents according to the optimization steps introduced in the thesis.
    /// Optimizations steps: flatten hierarchy, collapsing transient states.
    let rec optimize (activityNodes: BlechNode list) : BlechNode list = 
        // TODO Which optimization step comes first and how often are the steps done?
        match activityNodes with   
            | head :: tail -> optimizeSingleActivity head :: optimize tail
            | [] -> []

    /// Optimizes a single activity node.
    and private optimizeSingleActivity (activityNode: BlechNode) : BlechNode = 
        let actNodePayload = activityNode.Payload
        
        // Extract body.
        let isComplex = match actNodePayload.IsComplex with 
                        | IsComplex a -> a
                        | _ -> failwith "unexpected error, was not an activity node."// Should not happen here.
        let body = isComplex.Body
        let actPayload = isComplex.IsActivity
        
        //Flatten hierarchy inside activity.
        let flattenedBody = flattenHierarchyIfComplex (findInitNodeInHashSet body.Nodes) body

        // Collapse transient states.
        // TODO 

        // Put changed body in new node and return it.
        let newComplex : ComplexOrSimpleOrCobegin = IsComplex {Body = flattenedBody; IsActivity = actPayload; CaseClosingNode = None; IsAbort = IsAbort.Neither}
        BlechNode.Create {Label = actNodePayload.Label; IsComplex = newComplex; IsInitOrFinal = actNodePayload.IsInitOrFinal; StateCount = actNodePayload.StateCount; WasVisualized = NotVisualized}

    //______________________________FLATTEN HIERARCHY_______________________________________________________
    /// Flattens the hierarchy on a list of nodes subsequentially.
    and private callFlatHierarchyOnNodes (nodes : BlechNode list) (graph : VisGraph) : VisGraph = 
        match nodes with
            | head :: tail -> flattenHierarchyIfComplex head graph |> callFlatHierarchyOnNodes tail 
            | [] ->  graph

    /// Flattens a given graph if node is complex, else just call flattening method on successors.
    and private flattenHierarchyIfComplex (currentNode : BlechNode) (graph : VisGraph) : VisGraph = 
        // Is current node complex?
        let successsors = (Seq.toList currentNode.Successors)
        let currentGraph = match currentNode.Payload.IsComplex with
                            | IsSimple | IsActivityCall _ -> graph
                            | IsCobegin _ -> graph // TO NOTHING. TODO cobegin.
                            | IsComplex cmplx -> flattenHierarchy currentNode cmplx graph

        callFlatHierarchyOnNodes successsors currentGraph

    /// Elevates the inner body of a complex node to the level given in graph. Collapses hierarchies recursively regarding all hierarchies that are not caused by activites.
    and private flattenHierarchy (currentNode : BlechNode) (complex : ComplexNode) (graph : VisGraph) : VisGraph = 
        // Recursive hierarchy flattening call on inner graph.
        let innerGraph = flattenHierarchyIfComplex (findInitNodeInHashSet complex.Body.Nodes) (clone complex.Body)

        // TODO no final node?
        // 1. Change the status of the inner init/final state, so that they are regular states.
        // 2. Join inner graph with current graph. 
        // 4. Modify in- and outcoming edges from node and change their source/target to the final/init node of the inner graph, respecitvely.
        // 5. Respect the differences in handling edges (aborts, for example). Some completely new edges might have to be added.
        // 6. Remove node from graph.
        let init = findInitNodeInHashSet innerGraph.Nodes
        let final = findFinalNodeInHashSet innerGraph.Nodes
        let newInit = innerGraph.ReplacePayloadInByAndReturn init init.Payload.CopyWithSimpleComplexity
        let newFinal = innerGraph.ReplacePayloadInByAndReturn final final.Payload.CopyWithSimpleComplexity
        let incomingEdges = Seq.toList currentNode.Incoming
        let outgoingEdges = Seq.toList currentNode.Outgoing
        let joinedGraph : VisGraph = VisGraph.Join graph innerGraph
        
        // Add abort transitions according to the concept from the inner graph to either the former initial state of the inner graph or the case closing state, depending on the abort.
        match complex.IsAbort with
            | AbortWhen label -> List.map (addAbortEdgeToNode  complex.CaseClosingNode.Value label innerGraph) (findFirstAwaitNodeOnEveryPath newInit) |> ignore
            | AbortRepeat label -> List.map (addAbortEdgeToNode newInit label innerGraph) (findFirstAwaitNodeOnEveryPath newInit) |> ignore
            | IsAbort.Neither -> () // Do nothing.
        
        let updatedGraph = updateEdges incomingEdges newInit Target joinedGraph |> updateEdges outgoingEdges newFinal Source
        updatedGraph.RemoveNode currentNode
        updatedGraph

    /// Adds a list of new edges to the graph.
    /// New edges are based on the data given by the edges, the information whether source or target is to be changed and the given node to be the new source/target.
    /// Join Transitions are changed to immediate transitions.
    and private updateEdges (edgeList : BlechEdge list) (newTargetOrSource : BlechNode) (sourceOrTarget : SourceOrTarget) (graph : VisGraph): VisGraph = 
        match edgeList with 
            | head :: tail  ->  // Determine payload. Terminal transitions change to immdediate transitions
                                let payload = match head.Payload.Property with
                                                | IsAwait | IsConditional | IsImmediate | IsAbort -> head.Payload
                                                | IsTerminal -> head.Payload.CopyWithPropertyImmediate
                                match sourceOrTarget with
                                    | Source -> graph.AddEdge payload newTargetOrSource head.Target
                                    | Target -> graph.AddEdge payload head.Source newTargetOrSource
                                updateEdges tail newTargetOrSource sourceOrTarget graph
            | [] -> graph
    
    /// Adds an abort edge to the given graph with the given label, source and target.
    and private addAbortEdgeToNode (target : BlechNode) (label: string) (graph : VisGraph) (source : BlechNode) =     
        graph.AddEdge {Label = label; Property = IsAbort} source target

    //______________________________COLLAPSE IMMEDIATE TRANSITIONS_______________________________________________________        