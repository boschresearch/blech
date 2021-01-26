module Blech.Visualization.Optimization
    open Blech.Common.GenericGraph
    open Blech.Visualization.BlechVisGraph

    /// Keeps track of which edges have been optimized yet.
    let mutable optimizedEdges: (int * int) list = []

     //______________________________CENTRAL FUNCTION_______________________________________________________
    /// Optimizes the nodes and their contents according to the optimization steps introduced in the thesis.
    /// Optimizations steps: flatten hierarchy, collapsing transient states.
    let rec optimize (activityNodes: BlechNode list) : BlechNode list = 
        List.map optimizeSingleActivity activityNodes

    /// Optimizes a single activity node.
    and private optimizeSingleActivity (activityNode: BlechNode) : BlechNode = 
        printfn "Optimizing activity %s" activityNode.Payload.Label
        let actNodePayload = activityNode.Payload
        // Extract body.
        let isComplex = match actNodePayload.IsComplex with 
                        | IsComplex a -> a
                        | _ -> failwith "unexpected error, was not an activity node."// Should not happen here.
        let body = isComplex.Body
        let actPayload = isComplex.IsActivity
        
        //Flatten hierarchy inside activity.
        printfn "Flattening hierarchies."
        let flattenedBody = flattenHierarchyIfComplex (findInitNodeInHashSet body.Nodes) body

        // Collapse transient states.
        printfn "Collapsing transient states."
        optimizedEdges <- []
        let collapsenTransientStatesBody = collapseTransient flattenedBody

        // Put changed body in new node and return it.
        let newComplex : ComplexOrSimpleOrCobegin = IsComplex {Body = collapsenTransientStatesBody; IsActivity = actPayload; CaseClosingNode = None; IsAbort = Neither}
        BlechNode.Create{Label = actNodePayload.Label; 
                         IsComplex = newComplex; 
                         IsInitOrFinal = actNodePayload.IsInitOrFinal; 
                         StateCount = actNodePayload.StateCount; 
                         WasVisualized = NotVisualized; 
                         WasHierarchyOptimized = HierarchyOptimized}

    //______________________________FLATTEN HIERARCHY (NOT COBEGIN OR ACTIITY CALLS)_______________________________________________________
    /// Flattens a given graph if node is complex, else just call flattening method on successors.
    and private flattenHierarchyIfComplex (currentNode : BlechNode) (graph : VisGraph) : VisGraph = 
        //printfn "rein A"
        // Is current node complex? 
        // Do not call method on same item again when there are self-loops.
        let filterForUnoptimized = 
            (fun (e : BlechNode) -> match e.Payload.WasHierarchyOptimized with HierarchyOptimized -> false | NotHierarchyOptimized -> true)
        let successorsWithoutCurrent = (removeItem currentNode (Seq.toList currentNode.Successors))
        let unoptedSuccesssors = List.filter filterForUnoptimized successorsWithoutCurrent
        //List.map (fun (n : BlechNode)-> printfn "s%i" n.Payload.StateCount) unoptedSuccesssors |> ignore
        let currentGraph = match currentNode.Payload.IsComplex with
                            | IsSimple | IsActivityCall _ -> graph
                            | IsCobegin cmplx -> flattenHierarchyCobegin currentNode cmplx graph
                            | IsComplex cmplx -> flattenHierarchy currentNode cmplx graph

        currentNode.Payload.SetHierarchyOptimized

        //List.map (fun (n : BlechNode)-> printfn "succesor of s%i - s%i" currentNode.Payload.StateCount n.Payload.StateCount) unoptedSuccesssors |> ignore
        let res = callFlatHierarchyOnNodes unoptedSuccesssors currentGraph
        //printfn "raus A"
        res

    /// Flattens the hierarchy on a list of nodes subsequentially.
    and private callFlatHierarchyOnNodes (nodes : BlechNode list) (graph : VisGraph) : VisGraph = 
        //printfn "rein B"
        let r = List.fold (fun state e-> flattenHierarchyIfComplex e state) graph nodes
        //printfn "raus B"
        r

    /// Elevates the inner body of a complex node to the level given in graph. Collapses hierarchies recursively regarding all hierarchies that are not caused by activites.
        // 1. Change the status of the inner init/final state, so that they are regular states.
        // 2. Join inner graph with current graph. 
        // 4. Modify in- and outcoming edges from node and change their source/target to the final/init node of the inner graph, respecitvely.
        // 5. Respect the differences in handling edges (aborts, for example). Some completely new edges might have to be added.
        // 6. Remove node from graph.
    and private flattenHierarchy (currentNode : BlechNode) (complex : ComplexNode) (graph : VisGraph) : VisGraph = 
        // Recursive hierarchy flattening call on inner graph.
        let innerGraph = flattenHierarchyIfComplex (findInitNodeInHashSet complex.Body.Nodes) (complex.Body)
        // TODO no final node?
        //printfn "----->current node s%i" currentNode.Payload.StateCount
        let init = findInitNodeInHashSet innerGraph.Nodes
        let final = findFinalNodeInHashSet innerGraph.Nodes
        let replacedInit = innerGraph.ReplacePayloadInByAndReturn init (init.Payload.SetInitStatusOff)
        let replacedFinal = innerGraph.ReplacePayloadInByAndReturn final (final.Payload.SetFinalStatusOff)
        // Use above two with caution ! Not correct ones after joining graphs.
        let innerInitStateCount = replacedInit.Payload.StateCount
        let innerFinalStateCount = replacedFinal.Payload.StateCount

        let innerNodesIds = List.map (fun (n:BlechNode) -> n.Payload.StateCount) (Seq.toList innerGraph.Nodes)
        let joinedGraph = addGraphToGraph graph innerGraph
        let newInit = findNodeByStateCount innerInitStateCount joinedGraph
        let newFinal = findNodeByStateCount innerFinalStateCount joinedGraph

        // Add abort transitions according to the concept from the inner graph to either the former initial state of the inner graph or the case closing state, depending on the abort.
        match complex.IsAbort with
            | AbortWhen label -> List.map (addAbortEdgeToNode complex.CaseClosingNode.Value label joinedGraph) (findFirstAwaitNodeOnEveryPath newInit innerNodesIds) |> ignore
            | AbortRepeat label -> List.map (addAbortEdgeToNode newInit label joinedGraph) (findFirstAwaitNodeOnEveryPath newInit innerNodesIds) |> ignore
            | Neither -> () // Do nothing.

        // Update edges.
        let updatedGraph = updateEdgesFlattenHierarchy (Seq.toList currentNode.Incoming) newInit Target joinedGraph 
                            |> updateEdgesFlattenHierarchy (Seq.toList currentNode.Outgoing) newFinal Source

        //There is something wrong with the removal of the node. Find specific node and remove it.
        //if(currentNode.Payload.StateCount = 12) then 
        //printfn "before"; listNodes (Seq.toList updatedGraph.Nodes)
        //if(currentNode.Payload.StateCount = 12) then printfn "before"; listEdges (Seq.toList updatedGraph.Edges)
        //printfn "statecount %i" currentNode.Payload.StateCount
        let nodeToRemove = List.find (fun (n:BlechNode) -> n.Payload.StateCount = currentNode.Payload.StateCount) (Seq.toList updatedGraph.Nodes)
        updatedGraph.RemoveNode nodeToRemove
        //if(currentNode.Payload.StateCount = 12) then printfn "after"; listNodes (Seq.toList updatedGraph.Nodes)
        //if(currentNode.Payload.StateCount = 12) then printfn "after"; listEdges (Seq.toList updatedGraph.Edges)
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
                                                | IsConditionalTerminal -> head.Payload.CopyWithPropertyConditional
                                match sourceOrTarget with
                                    | Source -> //printfn "new source connecting s%i to s%i, label %s" newTargetOrSource.Payload.StateCount head.Target.Payload.StateCount head.Payload.Label;
                                                graph.AddEdge payload newTargetOrSource head.Target
                                    | Target -> //printfn "new target connecting s%i to s%i, label %s" head.Source.Payload.StateCount newTargetOrSource.Payload.StateCount head.Payload.Label; 
                                                graph.AddEdge payload head.Source newTargetOrSource
                                updateEdgesFlattenHierarchy tail newTargetOrSource sourceOrTarget graph
            | [] -> graph
    
    /// Adds an abort edge to the given graph with the given label, source and target.
    and private addAbortEdgeToNode (target : BlechNode) (label: string) (graph : VisGraph) (source : BlechNode) =     
        graph.AddEdge {Label = label; Property = IsAbort; WasOptimized = NotOptimized} source target

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
        printfn "length %i" edges.Length
        match edges with
            | head :: tail -> checkSingleEdgeForCollapse graph head |> checkEdgesForCollapse tail
            | [] -> graph

    /// Calls the recursive method on subsequent edges. Avoid edges that are self-loops.
    and private callSubsequentAndFilterAlreadyVisitedTargets (edges : BlechEdge List) (graph : VisGraph) : VisGraph =
        let filterForUnoptimizedEdges = 
            (fun (e : BlechEdge) -> not (List.contains (e.Source.Payload.StateCount, e.Target.Payload.StateCount) optimizedEdges))
        checkEdgesForCollapse (List.filter filterForUnoptimizedEdges edges) graph

    /// Updates the status of the current node in context of immediate transition deletion. 
    /// Depending on the final and init status of the other node (sourceOrTarget), which is to be deleted, the status of the given node changes.
    and updateStatusOfNodeDependingOfSuccessorOrPredecessor (current : BlechNode) (counterpart : BlechNode) (graph : VisGraph) : BlechNode = 
        let initChecked = match counterpart.Payload.IsInitOrFinal.Init with
                                        | IsInit -> graph.ReplacePayloadInByAndReturn current (current.Payload.SetInitStatusOn)
                                        | _ -> current

        let bothChecked = match counterpart.Payload.IsInitOrFinal.Final with
                                       | IsFinal -> graph.ReplacePayloadInByAndReturn initChecked (initChecked.Payload.SetInitStatusOn)
                                       | _ -> initChecked

        bothChecked

    /// Checks a single edge for collaps according to the specifications in the thesis. Checks outgoing transitions as ingoin transitions have been tested by a former step.
    /// Also calls the collapse of immediate trnaasitions recursively to complex nodes.
    // TODO this is not functional programming..
    and private checkSingleEdgeForCollapse (graph : VisGraph) (edge : BlechEdge) : VisGraph = 
        printfn "checking s%i - %s - edge s%i to s%i" edge.Source.Payload.StateCount (edge.Payload.Property.ToString()) edge.Source.Payload.StateCount edge.Target.Payload.StateCount
        
        //Recursive calls
        match edge.Source.Payload.IsComplex with 
            | IsComplex cmplx -> collapseTransient cmplx.Body
            | IsCobegin cbgn -> immediateCollapseCallOnCobegin cbgn graph
            | IsSimple | IsActivityCall _-> graph
        |> ignore

        let source = edge.Source
        let sourceOutgoings = (Seq.toList source.Outgoing)
        let target = edge.Target
        let targetIncomings = (Seq.toList target.Incoming)

        // Mark the current edge as optimized.
        //let updatedEdge = graph.AddEdgeAndReturn edge.Payload.CopyAsNotOptimized edge.Source edge.Target
        //graph.RemoveEdge edge
        optimizedEdges <- (source.Payload.StateCount, target.Payload.StateCount) :: optimizedEdges

        // Special case: between two nodes are a immediate and a abort transition.
        // Both are deleted, if target or source is simple and has only two outgoing/incoming transitions respecitvely.
        // If none of the two nodes can be deleted, only the abort is deleted, since it is unneccessary.
        if(sourceOutgoings.Length >= 2 && targetIncomings.Length >= 2 &&
            immediateAndAbortNode edge sourceOutgoings &&
            immediateAndAbortNode edge targetIncomings) then
            if source.Payload.IsComplex = IsSimple && source.Payload.Label.Equals "" && (Seq.toList source.Outgoing).Length = 2 then
                handleSourceDeletion source target graph
            else if target.Payload.IsComplex = IsSimple && target.Payload.Label.Equals "" && (Seq.toList target.Incoming).Length = 2 then
                handleTargetDeletion source target graph
            else 
                printf "here?"
                callSubsequentAndFilterAlreadyVisitedTargets (Seq.toList target.Outgoing) graph
        // Clear cases where the edge is not deleted.
        elif(sourceOutgoings.Length > 1 && targetIncomings.Length > 1 ||
             source.Payload.StateCount = target.Payload.StateCount ||
             edge.Payload.Property <> IsImmediate && edge.Payload.Property <> IsTerminal ||
             edge.Payload.Property = IsTerminal && not (edge.Payload.Label.Equals "") ||
             edge.Payload.Property = IsImmediate && not (edge.Payload.Label.Equals "")) then 
                printfn "case 1"
                callSubsequentAndFilterAlreadyVisitedTargets (Seq.toList target.Outgoing) graph
        else 
            // Can a) source or b) target be deleted (no label, no complexity)? If so, delete possible node. If not, immediate transition is not deleted.
            // If source is deleted, change the target of incoming nodes of the source to target. If deleted source is init state, change target to initial state. 
            // If target is deleted, change the source of outgoing nodes of the target to the source. If deleted source is final state, change source to final state.
            // If a final or initial state is removed, that status needs to be reassigned.
            // Target can not be deleted if it has multiple incomings, source can not be deleted if it has multiple outgoings.
            if source.Payload.IsComplex = IsSimple && source.Payload.Label.Equals "" && (Seq.toList source.Outgoing).Length = 1 then
                handleSourceDeletion source target graph
            else if target.Payload.IsComplex = IsSimple && target.Payload.Label.Equals "" && (Seq.toList target.Incoming).Length = 1 then
                handleTargetDeletion source target graph
            else if (Seq.toList target.Outgoing).Length > 0 then 
                printfn "case 4"
                callSubsequentAndFilterAlreadyVisitedTargets (Seq.toList target.Outgoing) graph
            else
                printfn "case 5"
                graph

    /// Updates the status of the target and reassigns source's incoming and deletes the source node (and not updated edges).
    and private handleSourceDeletion (source : BlechNode) (target : BlechNode) (graph : VisGraph) : VisGraph =  
        let statusChangedTarget = updateStatusOfNodeDependingOfSuccessorOrPredecessor target source graph
        let updatedTarget = updateEdgesCollapseImmediate (Seq.toList source.Incoming) statusChangedTarget Target graph
        printfn "case 2"
        //printfn "removing s%i" source.Payload.StateCount
        //List.map (fun (n:BlechEdge) -> printfn "s%i to s%i" n.Source.Payload.StateCount n.Target.Payload.StateCount) (Seq.toList source.Incoming) |> ignore 
        graph.RemoveNode source
        //printfn "-"
        callSubsequentAndFilterAlreadyVisitedTargets (Seq.toList updatedTarget.Outgoing) graph

    /// Updates the status of the source and reassigns source's incoming and deletes the target node (and not updated edges).
    and private handleTargetDeletion (source : BlechNode) (target : BlechNode) (graph : VisGraph) : VisGraph =  
        let statusChangedSource = updateStatusOfNodeDependingOfSuccessorOrPredecessor source target graph
        //List.map (fun (n:BlechEdge) -> printfn "s%i to s%i" n.Source.Payload.StateCount n.Target.Payload.StateCount) (Seq.toList target.Outgoing) |> ignore                         
        let updatedSource = updateEdgesCollapseImmediate (Seq.toList target.Outgoing) statusChangedSource Source graph
        printfn "case 3"
        //printfn "removing s%i" target.Payload.StateCount
        graph.RemoveNode target
        printfn "length.. %i" (Seq.toList updatedSource.Outgoing).Length
        List.map (fun (n:BlechEdge) -> printfn "s%i to s%i - %s" n.Source.Payload.StateCount n.Target.Payload.StateCount (n.Payload.Property.ToString())) (Seq.toList updatedSource.Outgoing) |> ignore                         
        callSubsequentAndFilterAlreadyVisitedTargets (Seq.toList updatedSource.Outgoing) graph

    /// Adds a list of new edges to the graph.
    /// New edges are based on the data given by the edges, the information whether source or target is to be changed and the given node to be the new source/target.
    and private updateEdgesCollapseImmediate (edgeList : BlechEdge list) (newTargetOrSource : BlechNode) (sourceOrTarget : SourceOrTarget) (graph : VisGraph) : BlechNode = 
        match edgeList with 
            | head :: tail  ->  match sourceOrTarget with
                                    | Source -> graph.AddEdge head.Payload.CopyAsNotOptimized newTargetOrSource head.Target
                                    | Target -> graph.AddEdge head.Payload.CopyAsNotOptimized head.Source newTargetOrSource
                                updateEdgesCollapseImmediate tail newTargetOrSource sourceOrTarget graph
            | [] -> newTargetOrSource

    /// Calls the immediate collapse on every graph of a cobegin body.
    and private immediateCollapseCallOnCobegin (regions : CobeginPayload) (graph : VisGraph) : VisGraph=
        match regions with 
            | (innerGraph, _) :: tail ->collapseTransient innerGraph |> immediateCollapseCallOnCobegin tail
            | [] -> graph