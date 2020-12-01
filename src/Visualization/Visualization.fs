module Blech.Visualization.Visualization

    open Blech.Frontend
    open Blech.Frontend.BlechTypes
    open Blech.Common
    open Blech.Common.GenericGraph
    open Blech.Visualization.BlechVisGraph


    /// Add an await statement to the graph connecting to the previous node.
    /// According to the 
    let private synthesize_await (input : VisGraph * Node<nodePayload, edgePayload>) (label : string) : (VisGraph * Node<nodePayload, edgePayload>) =
        // Extract.
        let graph = fst(input)
        let prevNode = snd(input)

        // New node.
        let newNode = graph.AddNode(new nodePayload("", IsSimple, false, false, PayloadAbsent))

        // New the edge.
        graph.AddEdge (new edgePayload(label, true, false, false, false, false)) prevNode newNode |> ignore

        (graph, newNode) 
       

    /// Synthesis of the body of an activity.
    let private synthesize_activity_body (stmts : Stmt list) : VisGraph =
        // Init.
        let graph = Graph.Empty()
        let init = graph.AddNode(new nodePayload("", IsSimple, true, false, PayloadAbsent))
        let mutable graphAndPrevNode : VisGraph * Node<nodePayload, edgePayload> = (graph, init)
       
        // Work the statements.
        for stmt in stmts do
            graphAndPrevNode <- match stmt with
                                        | Await (_, typedRhs) -> synthesize_await (graphAndPrevNode) (typedRhs.ToString())
            // ignore these for now.. DURCHBRUCH..
            // TODO
            //| ITE (range, typedRhs, stmtList, stmList)-> ()
            //| Cobegin (range, listOfStrengthAndStmts) -> ()
            //| WhileRepeat (range, typedRhs, stmtList) -> ()
            //| RepeatUntil (range, stmtList, typedRhs, bool) -> ()
            //| Preempt (range, preemeption, typedRhs, moment, stmtList) -> ()
            //| ActivityCall (range, qName, receiverOption, typedRhsList, typedLhsList) -> ()
            //| StmtSequence (stmtList) -> printf "loop this shit"
                                        | _ -> graphAndPrevNode // ignore all other statements and just return the construct as it was before.

        // connect last available noe to the final node. TODO only if available?
        let final = graph.AddNode(new nodePayload("", IsSimple, false, true, PayloadAbsent))
        graph.AddEdge (new edgePayload("", false, false, true, false, false)) (snd(graphAndPrevNode)) final |> ignore

        // return the graph
        fst(graphAndPrevNode)


    /// Synthesis of an activity.
    /// Gather data. 1 - name of activity, 2 - input and output data, 3 - construct activity body.
    let private synthesize_activity (entryPoint: SubProgramDecl) : VisGraph = 
        
        // Init Data.
        let name : string = entryPoint.name.label.ToString()

        let iparam : BlechVisGraph.paramList = 
            List.append (constructParamList entryPoint.inputs [])  (constructParamList2 entryPoint.globalInputs [])

        let oparam : BlechVisGraph.paramList = 
            List.append (constructParamList entryPoint.outputs [])  (constructParamList2 entryPoint.globalOutputsInScope []) 

        let body = synthesize_activity_body entryPoint.body

        // Init Graph.
        let graph = Graph.Empty()
        let activityPayloadPresent : activityPayloadPresent = PayloadPresent(new activityPayload(name, iparam, oparam, body))
        graph.AddNode(new nodePayload("", IsSimple, false, false, activityPayloadPresent)) |> ignore
        graph   


    /// Synthesis entry point. Pours the Blech code into a graph data modell (given by GenericGraph.fs).
    let private synthesize (entryPoint: SubProgramDecl) : (VisGraph) =
        // only synthesize if entry point is an actual activity and not a function.
        if entryPoint.isFunction then Graph.Empty() else synthesize_activity entryPoint 


    /// Synthesis start. Has side effects: unkown.
    let startSynthesis (arg : Result<TypeCheckContext * BlechModule, Diagnostics.Logger>) = 

        // Access values.
        let resultTuple : TypeCheckContext*BlechModule = 
            match arg with 
            | Ok a -> a
            | Error b -> failwith("Can not visualize errorous code.")

        let getTypeCheckContext : TypeCheckContext = 
            match resultTuple with
            | (a, _) -> a

        let blechModule : BlechModule =
            match resultTuple with
            | (_, b) -> b

        if blechModule.entryPoint.IsNone then failwith("Entry point needed for visualization.")
        let entryPoint: SubProgramDecl = blechModule.entryPoint.Value  // this is the entry point for my synthesis, this is the outermost activity of interest.

        // synthesize this activity (recurseviley if needed).
        let graph = synthesize entryPoint
        // TODO this assertion is not working.. 
        //if graph = Graph.Empty() then failwith ("Cannot visualize empty programm.")
        
        // Optimizations take place here.
        // TODO.

        // Generate sctx content.
        let sctxString = SctxGenerator.generate graph

        // Print sctx content to a file.
        SctxToFile.putToFile sctxString
        
        // ______________________________________________________________________
        // so that a let block is not the final part of the code... 
        let anotherString = resultTuple.ToString()
        let callMe = printfn (Printf.TextWriterFormat<_> anotherString)
        callMe