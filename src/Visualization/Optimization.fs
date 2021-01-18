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
        let collapsenTransientStatesBody = collapseTransient flattenedBody

        // Put changed body in new node and return it.
        let newComplex : ComplexOrSimpleOrCobegin = IsComplex {Body = collapsenTransientStatesBody; IsActivity = actPayload; CaseClosingNode = None; IsAbort = IsAbort.Neither}
        BlechNode.Create {Label = actNodePayload.Label; IsComplex = newComplex; IsInitOrFinal = actNodePayload.IsInitOrFinal; StateCount = actNodePayload.StateCount; WasVisualized = NotVisualized}

    //______________________________FLATTEN HIERARCHY (NOT COBEGIN OR ACTIITY CALLS)_______________________________________________________
    /// Flattens a given graph if node is complex, else just call flattening method on successors.
    and private flattenHierarchyIfComplex (currentNode : BlechNode) (graph : VisGraph) : VisGraph = 
        // Is current node complex?
        let successsors = (Seq.toList currentNode.Successors)
        let currentGraph = match currentNode.Payload.IsComplex with
                            | IsSimple | IsActivityCall _ -> graph
                            | IsCobegin cmplx -> flattenHierarchyCobegin currentNode cmplx graph
                            | IsComplex cmplx -> flattenHierarchy currentNode cmplx graph

        callFlatHierarchyOnNodes successsors currentGraph

    /// Flattens the hierarchy on a list of nodes subsequentially.
    and private callFlatHierarchyOnNodes (nodes : BlechNode list) (graph : VisGraph) : VisGraph = 
        match nodes with
            | head :: tail -> flattenHierarchyIfComplex head graph |> callFlatHierarchyOnNodes tail 
            | [] ->  graph

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
        let newInit = innerGraph.ReplacePayloadInByAndReturn init (init.Payload.CopyWithInitOrFinalStatusSetTo Neither)
        let newFinal = innerGraph.ReplacePayloadInByAndReturn final (final.Payload.CopyWithInitOrFinalStatusSetTo Neither)
        let incomingEdges = Seq.toList currentNode.Incoming
        let outgoingEdges = Seq.toList currentNode.Outgoing
        let joinedGraph : VisGraph = VisGraph.Join graph innerGraph
        
        // Add abort transitions according to the concept from the inner graph to either the former initial state of the inner graph or the case closing state, depending on the abort.
        match complex.IsAbort with
            | AbortWhen label -> List.map (addAbortEdgeToNode  complex.CaseClosingNode.Value label innerGraph) (findFirstAwaitNodeOnEveryPath newInit) |> ignore
            | AbortRepeat label -> List.map (addAbortEdgeToNode newInit label innerGraph) (findFirstAwaitNodeOnEveryPath newInit) |> ignore
            | IsAbort.Neither -> () // Do nothing.
        
        let updatedGraph = updateEdgesFlattenHierarchy incomingEdges newInit Target joinedGraph |> updateEdgesFlattenHierarchy outgoingEdges newFinal Source
        updatedGraph.RemoveNode currentNode
        updatedGraph

    /// Adds a list of new edges to the graph.
    /// New edges are based on the data given by the edges, the information whether source or target is to be changed and the given node to be the new source/target.
    /// Join Transitions are changed to immediate transitions.
    and private updateEdgesFlattenHierarchy (edgeList : BlechEdge list) (newTargetOrSource : BlechNode) (sourceOrTarget : SourceOrTarget) (graph : VisGraph): VisGraph = 
        match edgeList with 
            | head :: tail  ->  // Determine payload. Terminal transitions change to immdediate transitions
                                let payload = match head.Payload.Property with
                                                | IsAwait | IsConditional | IsImmediate | IsAbort -> head.Payload
                                                | IsTerminal -> head.Payload.CopyWithPropertyImmediate
                                match sourceOrTarget with
                                    | Source -> graph.AddEdge payload newTargetOrSource head.Target
                                    | Target -> graph.AddEdge payload head.Source newTargetOrSource
                                updateEdgesFlattenHierarchy tail newTargetOrSource sourceOrTarget graph
            | [] -> graph
    
    /// Adds an abort edge to the given graph with the given label, source and target.
    and private addAbortEdgeToNode (target : BlechNode) (label: string) (graph : VisGraph) (source : BlechNode) =     
        graph.AddEdge {Label = label; Property = IsAbort} source target

    //______________________________FLATTEN HIERARCHY (COBEGIN)_______________________________________________________
    /// Elevates the inner body of a cobegin node to the level given in graph, iff certain patterns are matched. 
    /// Collapses hierarchies recursively regarding all hierarchies that are not caused by activites.
    and private flattenHierarchyCobegin (currentNode : BlechNode) (complex : CobeginPayload) (graph : VisGraph) : VisGraph =
        // TODO implement
        graph

    //______________________________COLLAPSE IMMEDIATE TRANSITIONS_______________________________________________________ 
    /// Starting point for collapsing transient transitions.
    and private collapseTransient (graph : VisGraph) : VisGraph =
        let initNodes = findInitNodeInHashSet graph.Nodes
        checkEdgesForCollapse (Seq.toList initNodes.Outgoing) graph

    ///Method to iterate over an edge of list to check single edges.
    and private checkEdgesForCollapse (edges : BlechEdge list) (graph : VisGraph) : VisGraph = 
        match edges with
            | head :: tail -> checkSingleEdgeForCollapse graph head |> checkEdgesForCollapse tail
            | [] -> graph

    /// Checks a single edge for collaps according to the specifications in the thesis. Checks outgoing transitions as ingoin transitions have been tested by a former step.
    /// Also calls the collapse of immediate trnaasitions recursively to complex nodes.
    // TODO this is not functional programming..
    and private checkSingleEdgeForCollapse (graph : VisGraph) (edge : BlechEdge) : VisGraph = 
        // Recursive calls
        match edge.Source.Payload.IsComplex with 
            | IsComplex cmplx -> graph //collapseTransient cmplx.Body
            | IsCobegin cbgn -> graph //immediateCollapseCallOnCobegin cbgn graph
            | IsSimple | IsActivityCall _-> graph
        |> ignore

        let source = edge.Source
        let sourceOutgoings = (Seq.toList source.Outgoing)
        let target = edge.Target
        let targetIncomings = (Seq.toList target.Incoming)
        printf "checking edge from s%i to s%i" source.Payload.StateCount target.Payload.StateCount

        // Source initial and multiple outgoing?        
        // Target final and multiple incoming?
        // transition has condition?
        if((source.Payload.IsInitOrFinal = Init && sourceOutgoings.Length > 1) || 
            (target.Payload.IsInitOrFinal = Final && targetIncomings.Length > 1) ||
            edge.Payload.Property <> IsImmediate ||
            (edge.Payload.Property = IsImmediate && not (edge.Payload.Label.Equals ""))) then 
                printfn " case 1"
                checkEdgesForCollapse (Seq.toList target.Outgoing) graph
        else 
            // Can a) source or b) target be deleted (no label, no complexity)? If so, delete possible node. If not, immediate transition is not deleted.
            // If source is deleted, change the target of incoming nodes of the source to target. If deleted source is init state, change target to initial state. 
            // The two above are exclusive to each other.
            // If target is deleted, change the source of outgoing nodes of the target to the source. If deleted source is final state, change source to final state.
            // The two above are exclusive to each other.
            // If a final or initial state is removed, that status needs to be reassigned.
            if source.Payload.IsComplex = IsSimple && source.Payload.Label.Equals "" then
                printfn " case 2 "
                let updatedTarget = match source.Payload.IsInitOrFinal with
                                        | Init -> graph.ReplacePayloadInByAndReturn target (target.Payload.CopyWithInitOrFinalStatusSetTo Init)
                                        | _ -> updateEdgesCollapseImmediate (Seq.toList source.Incoming) target Target graph
                graph.RemoveNode source
                checkEdgesForCollapse (Seq.toList updatedTarget.Outgoing) graph
            else if target.Payload.IsComplex = IsSimple && target.Payload.Label.Equals "" then
                let updatedSource = match source.Payload.IsInitOrFinal with
                                        | Init -> graph.ReplacePayloadInByAndReturn source (source.Payload.CopyWithInitOrFinalStatusSetTo Final)
                                        | _ ->  updateEdgesCollapseImmediate (Seq.toList target.Outgoing) source Source graph
                graph.RemoveNode target
                printfn " case 3"
                checkEdgesForCollapse (Seq.toList updatedSource.Outgoing) graph
            else if (Seq.toList target.Outgoing).Length > 0 then 
                printfn " case 4"
                checkEdgesForCollapse (Seq.toList target.Outgoing) graph
            else
                printfn " case 5" 
                graph

    /// Adds a list of new edges to the graph.
    /// New edges are based on the data given by the edges, the information whether source or target is to be changed and the given node to be the new source/target.
    and private updateEdgesCollapseImmediate (edgeList : BlechEdge list) (newTargetOrSource : BlechNode) (sourceOrTarget : SourceOrTarget) (graph : VisGraph) : BlechNode = 
        match edgeList with 
            | head :: tail  ->  match sourceOrTarget with
                                    | Source -> graph.AddEdge head.Payload newTargetOrSource head.Target
                                    | Target -> graph.AddEdge head.Payload head.Source newTargetOrSource
                                updateEdgesCollapseImmediate tail newTargetOrSource sourceOrTarget graph
            | [] -> newTargetOrSource

    /// Calls the immediate collapse on every graph of a cobegin body.
    and private immediateCollapseCallOnCobegin (regions : CobeginPayload) (graph : VisGraph) : VisGraph=
        match regions with 
            | (innerGraph, _) :: tail ->collapseTransient innerGraph |> immediateCollapseCallOnCobegin tail
            | [] -> graph