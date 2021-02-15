module Blech.Visualization.Optimization
    open Blech.Common.GenericGraph
    open Blech.Frontend.CommonTypes
    open Blech.Visualization.BlechVisGraph

    //______________________________Global variables_______________________________________________________
    /// Keeps track of which edges have been optimized yet.
    /// First pair are the ids of the source. Second pair are the ids of the target.
    /// ((Source.StateCount, Source.SecondaryId), (Target.StateCount, Target.SecondaryId))
    let mutable private optimizedEdges: ((int * int) * (int * int)) list = []

    /// Keeping track of secondary id f
    let mutable private secondaryId = 0 

    /// Keeping track whether activities need to be inlined. 
    let mutable inlineActs = false

    //______________________________CENTRAL FUNCTION_______________________________________________________
    // Checks an activity node, whether it has a final state. Returns the name of the activity and a boolean inidacting the presence of a final state.
    let private checkForNameAndFinalNode(activityNode : BlechNode) : string * bool = 
        let actNodePayload = activityNode.Payload
        // Extract body.
        let isComplex = match actNodePayload.IsComplex with 
                            | IsComplex a -> a
                            | _ -> failwith "unexpected error, was not an activity node."// Should not happen here.

        //printfn "%s %b" actNodePayload.Label (isThereFinalNodeInHashSet isComplex.Body.Nodes)

        (actNodePayload.Label, isThereFinalNodeInHashSet isComplex.Body.Nodes)
    
    /// Optimizes the nodes and their contents according to the optimization steps introduced in the thesis.
    /// Optimizations steps: flatten hierarchy, collapsing transient states.
    let rec optimize (inlineActivities: bool) (entryPointName : string) (activityNodes: BlechNode list) : BlechNode list =
        inlineActs <- inlineActivities
        let actNameAndFinalNodesPairs = List.map checkForNameAndFinalNode activityNodes
        match inlineActivities with
            | true -> [optimizeSingleActivity activityNodes actNameAndFinalNodesPairs (List.find (fun (n:BlechNode) -> n.Payload.Label = entryPointName) activityNodes)]  
            | false -> let firstIt = List.map (optimizeSingleActivity activityNodes actNameAndFinalNodesPairs) activityNodes
                       // Doing it twice. Activities are optimized sequentially. Some information is different, after a activity was updated.
                       // TODO make this functionally? So that the part where the updated information is needed is done only?
                       let actNameAndFinalNodesPairs = List.map checkForNameAndFinalNode firstIt
                       List.map (optimizeSingleActivity firstIt actNameAndFinalNodesPairs) firstIt

    /// Optimizes a single activity node.
    and private optimizeSingleActivity (activityNodes: BlechNode list) (finalNodeInfo : (string * bool) list) (activityNode: BlechNode) : BlechNode = 
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
        let flattenedBody = flattenHierarchyIfComplex activityNodes (findInitNodeInHashSet body.Nodes) body

        // Collapse transient states.
        printfn "Collapsing transient states."
        optimizedEdges <- []
        let collapsenTransientStatesBody = collapseTransient finalNodeInfo flattenedBody

        // Put changed body in new node and return it.
        let newComplex : ComplexOrSimpleOrCobegin = IsComplex {Body = collapsenTransientStatesBody; IsActivity = actPayload; CaseClosingNode = {Opt = None}; IsAbort = Neither}
        BlechNode.Create{Label = actNodePayload.Label; 
                         IsComplex = newComplex; 
                         IsInitOrFinal = actNodePayload.IsInitOrFinal; 
                         StateCount = actNodePayload.StateCount;
                         SecondaryId = actNodePayload.SecondaryId; 
                         WasVisualized = NotVisualized; 
                         WasHierarchyOptimized = HierarchyOptimized}

    //______________________________FLATTEN HIERARCHY (NOT COBEGIN OR ACTIITY CALLS)_______________________________________________________
    /// Flattens a given graph if node is complex, else just call flattening method on successors.
    and private flattenHierarchyIfComplex (activityNodes: BlechNode list) (currentNode : BlechNode) (graph : VisGraph) : VisGraph = 
        //printfn "rein A"
        // Is current node complex? 
        // Do not call method on same item again when there are self-loops.
        let filterForUnoptimized = 
            (fun (e : BlechNode) -> match e.Payload.WasHierarchyOptimized with HierarchyOptimized -> false | NotHierarchyOptimized -> true)
        let successorsWithoutCurrent = (removeItem currentNode (Seq.toList currentNode.Successors))
        let unoptedSuccesssors = List.filter filterForUnoptimized successorsWithoutCurrent
        //List.map (fun (n : BlechNode)-> printfn "s%i" n.Payload.StateCount) unoptedSuccesssors |> ignore
        let currentGraph = match currentNode.Payload.IsComplex with
                            | IsSimple -> currentNode.Payload.SetHierarchyOptimized; graph
                            | IsActivityCall _ -> match inlineActs with
                                                    |true -> secondaryId <- secondaryId + 1
                                                             flattenHierarchyActivityCall activityNodes currentNode graph
                                                    | false -> graph
                            | IsCobegin cmplx -> flattenHierarchyCobegin activityNodes currentNode cmplx graph
                            | IsComplex cmplx -> flattenHierarchy activityNodes currentNode cmplx graph

        //List.map (fun (n : BlechNode)-> printfn "succesor of s%i - s%i" currentNode.Payload.StateCount n.Payload.StateCount) unoptedSuccesssors |> ignore
        let res = callFlatHierarchyOnNodes activityNodes unoptedSuccesssors currentGraph
        //printfn "raus A"
        res

    /// Flattens the hierarchy on a list of nodes subsequentially.
    and private callFlatHierarchyOnNodes (activityNodes: BlechNode list) (nodes : BlechNode list) (graph : VisGraph) : VisGraph = 
        //printfn "rein B"
        let r = List.fold (fun state e-> flattenHierarchyIfComplex activityNodes e state) graph nodes
        //printfn "raus B"
        r

    /// Elevates the inner body of a complex node to the level given in graph. Collapses hierarchies recursively regarding all hierarchies that are not caused by activites.
        // 1. Change the status of the inner init/final state, so that they are regular states.
        // 2. Join inner graph with current graph. 
        // 4. Modify in- and outcoming edges from node and change their source/target to the final/init node of the inner graph, respecitvely.
        // 5. Respect the differences in handling edges (aborts, for example). Some completely new edges might have to be added.
        // 6. Remove node from graph.
    and private flattenHierarchy (activityNodes: BlechNode list) (currentNode : BlechNode) (complex : ComplexNode) (graph : VisGraph) : VisGraph = 
        // Recursive hierarchy flattening call on inner graph.
        let complexCloned = clone complex.Body

        // Adjust inner. Replace the payload.
        List.map (fun (n:BlechNode) -> complexCloned.ReplacePayloadInBy n (n.Payload.SetSecondaryId secondaryId)) (Seq.toList complexCloned.Nodes) |> ignore
        let innerGraph = flattenHierarchyIfComplex activityNodes (findInitNodeInHashSet complexCloned.Nodes) complexCloned
        
        //printfn "----->current node s%i%i" currentNode.Payload.StateCount currentNode.Payload.SecondaryId

        // Init.
        let init = findInitNodeInHashSet innerGraph.Nodes
        let replacedInit = innerGraph.ReplacePayloadInByAndReturn init (init.Payload.SetInitStatusOff)
        let innerInitStateCount = replacedInit.Payload.StateCount
        let innerInitSecondaryId = replacedInit.Payload.SecondaryId
        let innerNodesIds = List.map findIds (Seq.toList innerGraph.Nodes)
        let finalNodePresent = isThereFinalNodeInHashSet innerGraph.Nodes
        
        let initGraphPair = 
            match finalNodePresent with 
                | true ->
                    let final = findFinalNodeInHashSet innerGraph.Nodes
                    let replacedFinal = innerGraph.ReplacePayloadInByAndReturn final (final.Payload.SetFinalStatusOff)
                    let innerFinalStateCount = replacedFinal.Payload.StateCount
                    let innerFinalSecondary = replacedFinal.Payload.SecondaryId
                    let joinedGraph = addGraphToGraph graph innerGraph  
                    
                    let newInit = findNodeByStateCount innerInitStateCount innerInitSecondaryId joinedGraph
                    let newFinal = findNodeByStateCount innerFinalStateCount innerFinalSecondary joinedGraph

                    // Update edges.
                    (updateEdgesFlattenHierarchy (Seq.toList currentNode.Incoming) newInit Target joinedGraph 
                        |> updateEdgesFlattenHierarchy (Seq.toList currentNode.Outgoing) newFinal Source
                   , newInit)
                | false -> 
                    let joinedGraph = addGraphToGraph graph innerGraph
                    let newInit = findNodeByStateCount innerInitStateCount innerInitSecondaryId joinedGraph
            
                    // Update edges.
                    (updateEdgesFlattenHierarchy (Seq.toList currentNode.Incoming) newInit Target joinedGraph, newInit)
        let updatedGraph = fst initGraphPair
        let newInit = snd initGraphPair

        // Add abort transitions according to the concept from the inner graph to either the former initial state of the inner graph or the case closing state, depending on the abort.
        // TODO there has got to be some possible optimization here.
        match complex.IsAbort with
            | AbortWhen label -> //listNodes (Seq.toList updatedGraph.Nodes)
                                 // printfn "lf s%i%i" (complex.CaseClosingNode.Value.Payload.StateCount) (complex.CaseClosingNode.Value.Payload.BrokenActCallId)
                                 let caseClosingNode = findNodeByStateCount (complex.CaseClosingNode.StateCount) (complex.CaseClosingNode.SecondaryId) updatedGraph
                                 let firstAwaitAndSubsequentConstruct = findFirstAwaitNodeOnEveryPath newInit innerNodesIds [findIds newInit]
                                 let subsequentNodes = frst3 firstAwaitAndSubsequentConstruct
                                 match scnd3 firstAwaitAndSubsequentConstruct with 
                                        | Some a -> addAbortEdgeToNode caseClosingNode label updatedGraph a
                                        | None -> () // Do nothing.       
                                 List.map (addAbortEdgeToNode caseClosingNode label updatedGraph) subsequentNodes |> ignore
            | AbortRepeat label -> let firstAwaitAndSubsequentConstruct = findFirstAwaitNodeOnEveryPath newInit innerNodesIds [findIds newInit]
                                   let subsequentNodes = frst3 firstAwaitAndSubsequentConstruct
                                   match scnd3 firstAwaitAndSubsequentConstruct with 
                                        | Some a -> addAbortEdgeToNode newInit label updatedGraph a
                                        | None -> () // Do nothing. 
                                   List.map (addAbortEdgeToNode newInit label updatedGraph) subsequentNodes |> ignore
            | Neither -> () // Do nothing.

        //There is something wrong with the removal of the node. Find specific node and remove it.
        //if(currentNode.Payload.StateCount = 12) then 
        //printfn "before"; listNodes (Seq.toList updatedGraph.Nodes)
        //if(currentNode.Payload.StateCount = 12) then printfn "before"; listEdges (Seq.toList updatedGraph.Edges)
        //printfn "statecount %i" currentNode.Payload.StateCount
        //printfn " removing s%i%i" currentNode.Payload.StateCount currentNode.Payload.BrokenActCallId
        let nodeToRemove = List.find (matchNodes currentNode) (Seq.toList updatedGraph.Nodes)
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
                                    | Source -> //printfn "new source connecting s%i%i to s%i%i" newTargetOrSource.Payload.StateCount newTargetOrSource.Payload.SecondaryId head.Target.Payload.StateCount head.Target.Payload.SecondaryId;
                                                graph.AddEdge payload newTargetOrSource head.Target
                                    | Target -> //printfn "new target connecting s%i%i to s%i%i" head.Source.Payload.StateCount head.Source.Payload.SecondaryId newTargetOrSource.Payload.StateCount newTargetOrSource.Payload.SecondaryId; 
                                                graph.AddEdge payload head.Source newTargetOrSource
                                updateEdgesFlattenHierarchy tail newTargetOrSource sourceOrTarget graph
            | [] -> graph
    
    /// Adds an abort edge to the given graph with the given label, source and target.
    and private addAbortEdgeToNode (target : BlechNode) (label: string) (graph : VisGraph) (source : BlechNode) =     
        graph.AddEdge {Label = label; Property = IsAbort; WasOptimized = NotOptimized} source target

    //______________________________FLATTEN HIERARCHY (ACT CALL)_______________________________________________________
    /// Elevates the inner graph of another activity to a higher level. Activity is given by activityNodes. Current node is an activity call that is to be deleted.
    and private flattenHierarchyActivityCall (activityNodes: BlechNode list) (currentNode : BlechNode) (graph : VisGraph) : VisGraph = 
        // Find correct activity from list.
        let activityNode = List.find (fun (e:BlechNode) -> e.Payload.Label = currentNode.Payload.Label) activityNodes
        //printfn "activity %s, curr S%i%i" activityNode.Payload.Label currentNode.Payload.StateCount currentNode.Payload.SecondaryId
        let cmplx = match activityNode.Payload.IsComplex with 
                        | IsComplex a -> a
                        | _ -> failwith "unexpected error, was not an activity node."// Should not happen here.

        flattenHierarchy activityNodes currentNode cmplx graph

    //______________________________FLATTEN HIERARCHY (COBEGIN)_______________________________________________________
    /// Adds an  edge to the given graph with the given label, source and target and given property.
    and private addEdgeToNode (target : BlechNode) (property : EdgeProperty) (label: string) (graph : VisGraph) (source : BlechNode) =     
        graph.AddEdge {Label = label; Property = property; WasOptimized = NotOptimized} source target
     
    /// Adds an immediate or termintation edge to the given graph with the given label, source and target. Distinction depends on complexity of the source.
    and private addImmedOrTerminEdgeToNode (target : BlechNode) (label: string) (graph : VisGraph) (source : BlechNode) =     
        match source.Payload.IsComplex with
            | IsSimple -> graph.AddEdge {Label = label; Property = IsImmediate; WasOptimized = NotOptimized} source target
            | _ -> graph.AddEdge {Label = label; Property = IsTerminal; WasOptimized = NotOptimized} source target
    
    /// Checks, whether a graph contains only a single await statement.
    // TODO seriously with this method? Rework this for the love of 42. It works, but come on.
    and private onlyAwaitStmt (graph : VisGraph) : bool = 
        // This step is executed pre immediate-transition optimization.
        // Hence a single await statement should look like this:
        // initial -await- regular_node -immediate- final
        let init = findInitNodeInHashSet (graph.Nodes)
        match (Seq.toList init.Outgoing).Length = 1 with
            | true ->   let possibleAwaitEdge = (Seq.toList init.Outgoing).[0]
                        match possibleAwaitEdge.Payload.Property = IsAwait with
                            | true ->   let awaitTarget = possibleAwaitEdge.Target
                                        match (Seq.toList awaitTarget.Outgoing).Length = 1 with
                                            | true -> match (Seq.toList awaitTarget.Outgoing).[0].Target.Payload.IsInitOrFinal.IsFinalBool with
                                                        | true -> true
                                                        | false -> false
                                            | false -> false
                            | false -> false
            | false -> false

    // Checks for a pair of regions, if there is one weak region, while the other non-confirmed weak region contains only exactly one await statement.
    and private checkRegionWeakAndContainAwait (firstR : VisGraph * Strength) (secondR : VisGraph * Strength) : bool =
        //printfn "%b" (onlyAwaitStmt (fst secondR))
        //printfn "%b" (onlyAwaitStmt (fst firstR))
        (snd firstR = Weak && onlyAwaitStmt (fst secondR)) || (snd secondR = Weak && onlyAwaitStmt (fst firstR))    
    
    /// In a pair of regions, order them so that the weak region that does not contain only an await statement to come first. The latter is the condition of the await and its strength.
    /// This method has the constraint that the two regions return true when put in the method checkRegionWeakAndContainAwait.
    and private orderRegions (firstR : VisGraph * Strength) (secondR : VisGraph * Strength) : (VisGraph * Strength) * (string * Strength) =
        if not (checkRegionWeakAndContainAwait firstR secondR) then failwith "The given regions are not fit to be used in this method."
        let getAwaitCond = fun (graph : VisGraph) -> (Seq.toList (findInitNodeInHashSet graph.Nodes).Outgoing).[0].Payload.Label                                         

        if (snd firstR = Weak && onlyAwaitStmt (fst secondR)) then
            (firstR, (getAwaitCond (fst secondR), snd secondR))
        else 
            (secondR, (getAwaitCond (fst firstR), snd firstR))

    /// Elevates the inner body of a cobegin node to the level given in graph, iff certain patterns are matched. 
    /// Collapses hierarchies recursively regarding all hierarchies that are not caused by activites for every branch.
    and private flattenHierarchyCobegin (activityNodes: BlechNode list) (currentNode : BlechNode) (complex : CobeginPayload) (graph : VisGraph) : VisGraph =
        // Call flattening recursively on branches.
        List.map (fun (b : VisGraph * Strength) -> (flattenHierarchyIfComplex activityNodes (findInitNodeInHashSet (fst b).Nodes) (fst b))) complex.Content |> ignore

        // TODO extract this part, pretty similar to method "flattenHierarchy
        // Find pattern and elevate.
        // 1. Two regions, at least one weak. Other must contain a single await statement ONLY
        let cond1 = complex.Content.Length = 2 && checkRegionWeakAndContainAwait complex.Content.[0] complex.Content.[1]
        //printfn "%b" cond1
        if cond1 then
            //printfn "%b" (checkRegionWeakAndContainAwait complex.Content.[0] complex.Content.[1])
            let orderedPairOfRegions = orderRegions complex.Content.[0] complex.Content.[1]
            let graphToBeElevated = clone (fst (fst orderedPairOfRegions))

            //printfn "----->current node s%i" currentNode.Payload.StateCount
            // Init.
            let init = findInitNodeInHashSet graphToBeElevated.Nodes
            let replacedInit = graphToBeElevated.ReplacePayloadInByAndReturn init (init.Payload.SetInitStatusOff)
            let innerInitStateCount = replacedInit.Payload.StateCount
            let innerInitSecondaryId = replacedInit.Payload.SecondaryId
            let innerNodesIds = List.map findIds (Seq.toList graphToBeElevated.Nodes)
            let finalNodePresent = isThereFinalNodeInHashSet graphToBeElevated.Nodes
            let innerFinalStateCountAndSecondaryIfPresent = stateCountAndSecondaryOfFinalNodeIfPresent graphToBeElevated.Nodes

            let initGraphPair = 
                match finalNodePresent with 
                    | true ->
                        let final = findFinalNodeInHashSet graphToBeElevated.Nodes
                        graphToBeElevated.ReplacePayloadInByAndReturn final (final.Payload.SetFinalStatusOff) |> ignore

                        let joinedGraph = addGraphToGraph graph graphToBeElevated
                        let newInit = findNodeByStateCount innerInitStateCount innerInitSecondaryId joinedGraph

                        // Update edges. Not outgoing ones, they are special for the cobegin pattern and added explicitly. Edges such as aborts can not occur.
                        (updateEdgesFlattenHierarchy (Seq.toList currentNode.Incoming) newInit Target joinedGraph,
                         newInit)
                    | false -> 
                        let joinedGraph = addGraphToGraph graph graphToBeElevated
                        let newInit = findNodeByStateCount innerInitStateCount innerInitSecondaryId joinedGraph
                
                        // Update edges.
                        (updateEdgesFlattenHierarchy (Seq.toList currentNode.Incoming) newInit Target joinedGraph, newInit)
            let updatedGraph = fst initGraphPair
            let newInit = snd initGraphPair

            // Add transitions according to the concept from the inner graph to the case closing state.
            let caseClosingNode = findNodeByStateCount (complex.CaseClosingNode.StateCount) (complex.CaseClosingNode.SecondaryId) updatedGraph
            let findFirstAwaitConstruct = (findFirstAwaitNodeOnEveryPath newInit innerNodesIds [findIds newInit])
            let allAwaitAndSubsequentNodesInSupgraph = frst3 findFirstAwaitConstruct
            // First await.
            match scnd3 findFirstAwaitConstruct with | Some a -> addEdgeToNode caseClosingNode IsAwait (fst (snd orderedPairOfRegions)) updatedGraph a
                                                     | None -> () // Do nothing.                  
            //All nodes after first await.
            List.map (addEdgeToNode caseClosingNode IsImmediate (fst (snd orderedPairOfRegions)) updatedGraph) allAwaitAndSubsequentNodesInSupgraph |> ignore

            // Add edge from last to case closing, depending on strength of await-region. Edge is a conditionsless edge. ( Is termination edge if source is complex.)
            if (snd (snd orderedPairOfRegions)) = Weak && finalNodePresent then
                let innerStateIds = innerFinalStateCountAndSecondaryIfPresent.Value
                addImmedOrTerminEdgeToNode 
                    caseClosingNode
                    ""
                    updatedGraph 
                    (findNodeByStateCount (fst innerStateIds) (snd innerStateIds) updatedGraph)

            let nodeToRemove = List.find (matchNodes currentNode) (Seq.toList updatedGraph.Nodes)
            updatedGraph.RemoveNode nodeToRemove
            updatedGraph
        else
           graph

    //______________________________COLLAPSE IMMEDIATE TRANSITIONS_______________________________________________________ 
    /// Starting point for collapsing transient transitions.
    and private collapseTransient (finalNodeInfo : (string * bool) list) (graph : VisGraph) : VisGraph =
        let initNodes = findInitNodeInHashSet graph.Nodes
        checkEdgesForCollapse finalNodeInfo (Seq.toList initNodes.Outgoing) graph

    ///Method to iterate over an edge of list to check single edges.
    and private checkEdgesForCollapse (finalNodeInfo : (string * bool) list) (edges : BlechEdge list) (graph : VisGraph) : VisGraph = 
        //printfn "length %i" edges.Length
        match edges with
            | head :: tail -> checkSingleEdgeForCollapse finalNodeInfo graph head |> checkEdgesForCollapse finalNodeInfo tail
            | [] -> graph

    /// Calls the recursive method on subsequent edges. Avoid edges that are self-loops.
    and private callSubsequentAndFilterAlreadyVisitedTargets (finalNodeInfo : (string * bool) list) (edges : BlechEdge List) (graph : VisGraph) : VisGraph =
        let filterForUnoptimizedEdges = fun e -> not (List.contains (convertToIdTuple e) optimizedEdges)
        checkEdgesForCollapse finalNodeInfo (List.filter filterForUnoptimizedEdges edges) graph

    /// Updates the status of the current node in context of immediate transition deletion. 
    /// Depending on the final and init status of the other node (sourceOrTarget), which is to be deleted, the status of the given node changes.
    and updateStatusOfNodeDependingOfSuccessorOrPredecessor (finalNodeInfo : (string * bool) list) (current : BlechNode) (counterpart : BlechNode) (graph : VisGraph) : BlechNode = 
        let initChecked = match counterpart.Payload.IsInitOrFinal.Init with
                                        | IsInit -> graph.ReplacePayloadInByAndReturn current (current.Payload.SetInitStatusOn)
                                        | _ -> current

        let bothChecked = match counterpart.Payload.IsInitOrFinal.Final with
                            | IsFinal -> // If current is an activity call that has a final node, reassign final status. Without final node, do not reassign.
                                         let reassignFinal = nodeIsActivityCallAndHasFinalNode current finalNodeInfo 
                                         if reassignFinal then
                                            graph.ReplacePayloadInByAndReturn initChecked (initChecked.Payload.SetFinalStatusOn)
                                         else
                                            initChecked
                            | _ -> initChecked
        bothChecked

    /// Checks a single edge for collaps according to the specifications in the thesis. Checks outgoing transitions as ingoin transitions have been tested by a former step.
    /// Also calls the collapse of immediate trnaasitions recursively to complex nodes.
    // TODO this is not functional programming..
    and private checkSingleEdgeForCollapse (finalNodeInfo : (string * bool) list) (graph : VisGraph) (edge : BlechEdge) : VisGraph =
        
        //Recursive calls
        match edge.Source.Payload.IsComplex with 
            | IsComplex cmplx -> collapseTransient finalNodeInfo cmplx.Body
            | IsCobegin cbgn -> immediateCollapseCallOnCobegin finalNodeInfo cbgn.Content graph
            | IsSimple | IsActivityCall _-> graph
        |> ignore

        let source = edge.Source
        let sourceOutgoings = (Seq.toList source.Outgoing)
        let target = edge.Target
        let targetIncomings = (Seq.toList target.Incoming)

        // Mark the current edge as optimized.
        optimizedEdges <- convertToIdTuple edge :: optimizedEdges

        //printfn "checking s%i - %s - edge s%i%i to s%i%i - %s - target in %i" edge.Source.Payload.StateCount (edge.Payload.Property.ToString()) edge.Source.Payload.StateCount edge.Source.Payload.SecondaryId edge.Target.Payload.StateCount edge.Target.Payload.SecondaryId edge.Payload.Label (Seq.toList edge.Target.Incoming).Length

        // Special cases. 
        // Only immediate transitions between the source and edge.
        let specialCase1 = sourceOutgoings.Length >= 2 && targetIncomings.Length >= 2 &&
                            onlyImmediatesOrConditionals edge
        // Special case, abort and termination transition. Termination transition origins in an activity call a complex node or a cobegin without final node.
        // Only delete edge, if the current edge is the terminal edge.
        let specialCase2 =  (nodeIsActivityCallAndHasNoFinalNode source finalNodeInfo ||
                             (match source.Payload.IsComplex with
                                    | IsComplex cmplx ->not (isThereFinalNodeInHashSet cmplx.Body.Nodes)                    
                                    | IsCobegin cbgn -> not (isThereFinalNodeInCobegin cbgn.Content)
                                    | _ -> false)) &&
                            sourceOutgoings.Length >= 2 && targetIncomings.Length >= 2 &&
                            specifiedAndAbortEdge IsTerminal edge sourceOutgoings &&
                            specifiedAndAbortEdge IsTerminal edge targetIncomings &&
                            edge.Payload.Property = IsTerminal
        // Special case: between two nodes are a immediate and a abort transition.
        // Both are deleted, if target or source is simple and has only two outgoing/incoming transitions respecitvely.
        // Simplicity is checked after this condition is met.
        // This can only be checked after specialCase1 was checked !!
        let specialCase3 = sourceOutgoings.Length >= 2 && targetIncomings.Length >= 2 &&
                            specifiedAndAbortEdge IsImmediate edge sourceOutgoings &&
                            specifiedAndAbortEdge IsImmediate edge targetIncomings

        //printfn "%b" (nodeIsActivityCallAndHasNoFinalNode source finalNodeInfo)
        //printfn "case3: %b" specialCase3
        //printfn "final node? %b" (match source.Payload.IsComplex with
                                    //| IsComplex cmplx ->not (isThereFinalNodeInHashSet cmplx.Body.Nodes)                    
                                    //| IsCobegin cbgn -> not (isThereFinalNodeInCobegin cbgn.Content)
                                    //| _ -> false)

        if(specialCase1) then
            //printfn "case 1"
            if source.Payload.IsComplex = IsSimple && source.Payload.Label.Equals "" then
                handleSourceDeletion finalNodeInfo source target graph
            else if target.Payload.IsComplex = IsSimple && target.Payload.Label.Equals "" then
                handleTargetDeletion finalNodeInfo source target graph
            else    
                callSubsequentAndFilterAlreadyVisitedTargets finalNodeInfo (Seq.toList target.Outgoing) graph
        elif(specialCase2) then
            //printfn "case 2"
            graph.RemoveEdge edge
            callSubsequentAndFilterAlreadyVisitedTargets finalNodeInfo (Seq.toList target.Outgoing) graph
        elif(specialCase3) then
            //printfn "case 3"
            if source.Payload.IsComplex = IsSimple && source.Payload.Label.Equals "" && (Seq.toList source.Outgoing).Length = 2 then
                handleSourceDeletion finalNodeInfo source target graph
            else if target.Payload.IsComplex = IsSimple && target.Payload.Label.Equals "" && (Seq.toList target.Incoming).Length = 2 then
                handleTargetDeletion finalNodeInfo source target graph
            else
                callSubsequentAndFilterAlreadyVisitedTargets finalNodeInfo (Seq.toList target.Outgoing) graph
        // Clear cases where the edge is not deleted.
        elif(sourceOutgoings.Length > 1 && targetIncomings.Length > 1 ||
             matchNodes source target ||
             edge.Payload.Property <> IsImmediate && edge.Payload.Property <> IsTerminal ||
             edge.Payload.Property = IsTerminal && not (edge.Payload.Label.Equals "") ||
             edge.Payload.Property = IsImmediate && not (edge.Payload.Label.Equals "")) then 
                //printfn "case 4"
                callSubsequentAndFilterAlreadyVisitedTargets finalNodeInfo (Seq.toList target.Outgoing) graph
        else 
            // Can a) source or b) target be deleted (no label, no complexity)? If so, delete possible node. If not, immediate transition is not deleted.
            // If source is deleted, change the target of incoming nodes of the source to target. If deleted source is init state, change target to initial state. 
            // If target is deleted, change the source of outgoing nodes of the target to the source. If deleted source is final state, change source to final state.
            // If a final or initial state is removed, that status needs to be reassigned.
            // Target can not be deleted if it has multiple incomings, source can not be deleted if it has multiple outgoings.
            //printfn "case 5"
            if source.Payload.IsComplex = IsSimple && source.Payload.Label.Equals "" && (Seq.toList source.Outgoing).Length = 1 then
                //printfn "case 5.1"
                handleSourceDeletion finalNodeInfo source target graph
            else if target.Payload.IsComplex = IsSimple && target.Payload.Label.Equals "" && (Seq.toList target.Incoming).Length = 1 then
                //printfn "case 5.2"
                handleTargetDeletion finalNodeInfo source target graph
            else if (Seq.toList target.Outgoing).Length > 0 then 
                //printfn "case 5.3"
                callSubsequentAndFilterAlreadyVisitedTargets finalNodeInfo (Seq.toList target.Outgoing) graph
            else
                //printfn "case 5.4"
                graph

    /// Updates the status of the target and reassigns source's incoming and deletes the source node (and not updated edges).
    and private handleSourceDeletion (finalNodeInfo : (string * bool) list) (source : BlechNode) (target : BlechNode) (graph : VisGraph) : VisGraph =  
        let statusChangedTarget = updateStatusOfNodeDependingOfSuccessorOrPredecessor finalNodeInfo target source graph
        let updatedTarget = updateEdgesCollapseImmediate (Seq.toList source.Incoming) statusChangedTarget Target graph
        //printfn "case 2"
        //printfn "removing s%i" source.Payload.StateCount
        //List.map (fun (n:BlechEdge) -> printfn "s%i to s%i" n.Source.Payload.StateCount n.Target.Payload.StateCount) (Seq.toList source.Incoming) |> ignore 
        graph.RemoveNode source
        //printfn "-"
        callSubsequentAndFilterAlreadyVisitedTargets finalNodeInfo (Seq.toList updatedTarget.Outgoing) graph

    /// Updates the status of the source and reassigns source's incoming and deletes the target node (and not updated edges).
    and private handleTargetDeletion (finalNodeInfo : (string * bool) list) (source : BlechNode) (target : BlechNode) (graph : VisGraph) : VisGraph =  
        let statusChangedSource = updateStatusOfNodeDependingOfSuccessorOrPredecessor finalNodeInfo source target graph
        //List.map (fun (n:BlechEdge) -> printfn "s%i to s%i" n.Source.Payload.StateCount n.Target.Payload.StateCount) (Seq.toList target.Outgoing) |> ignore                         
        let updatedSource = updateEdgesCollapseImmediate (Seq.toList target.Outgoing) statusChangedSource Source graph
        //printfn "case 3"
        //printfn "removing s%i" target.Payload.StateCount
        graph.RemoveNode target
        //printfn "length.. %i" (Seq.toList updatedSource.Outgoing).Length
        //List.map (fun (n:BlechEdge) -> printfn "s%i to s%i - %s" n.Source.Payload.StateCount n.Target.Payload.StateCount (n.Payload.Property.ToString())) (Seq.toList updatedSource.Outgoing) |> ignore                         
        callSubsequentAndFilterAlreadyVisitedTargets finalNodeInfo (Seq.toList updatedSource.Outgoing) graph

    /// Adds a list of new edges to the graph.
    /// New edges are based on the data given by the edges, the information whether source or target is to be changed and the given node to be the new source/target.
    /// If the edge is immediate and the new source is a complex node (everytime it is not simple), change the edge to a termination edge.
    and private updateEdgesCollapseImmediate (edgeList : BlechEdge list) (newTargetOrSource : BlechNode) (sourceOrTarget : SourceOrTarget) (graph : VisGraph) : BlechNode = 
        match edgeList with 
            | head :: tail  ->  match sourceOrTarget with
                                    | Source -> if newTargetOrSource.Payload.IsComplex <> IsSimple && (head.Payload.Property = IsImmediate || head.Payload.Property = IsConditional) then
                                                    if (head.Payload.Property = IsImmediate) then 
                                                        //printfn "A"
                                                        graph.AddEdge head.Payload.CopyAsNotOptimized.CopyWithPropertyTerminal newTargetOrSource head.Target  
                                                    else 
                                                        //printfn "B"
                                                        graph.AddEdge head.Payload.CopyAsNotOptimized.CopyWithPropertyConditionalTerminal newTargetOrSource head.Target
                                                else
                                                    //printfn "C"
                                                    graph.AddEdge head.Payload.CopyAsNotOptimized newTargetOrSource head.Target 
                                                //graph.AddEdge head.Payload.CopyAsNotOptimized newTargetOrSource head.Target
                                    | Target -> graph.AddEdge head.Payload.CopyAsNotOptimized head.Source newTargetOrSource
                                updateEdgesCollapseImmediate tail newTargetOrSource sourceOrTarget graph
            | [] -> newTargetOrSource

    /// Calls the immediate collapse on every graph of a cobegin body.
    and private immediateCollapseCallOnCobegin (finalNodeInfo : (string * bool) list) (regions : (VisGraph * Strength) list) (graph : VisGraph) : VisGraph=
        match regions with 
            | (innerGraph, _) :: tail ->collapseTransient finalNodeInfo innerGraph |> immediateCollapseCallOnCobegin finalNodeInfo tail
            | [] -> graph