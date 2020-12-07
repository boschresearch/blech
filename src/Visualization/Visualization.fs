module Blech.Visualization.Visualization

    open Blech.Frontend
    open Blech.Frontend.BlechTypes
    open Blech.Common
    open Blech.Common.GenericGraph
    open Blech.Visualization.BlechVisGraph

    /// Renders the string from the TypedRhs to a more presentable form.
    let private renderRhsString (rhs : TypedRhs) : string =
       let theString = rhs.ToString ()
       // TODO some sort of rendering to make activity.input to input.
       theString

    /// Add an await statement to the graph connecting to the previous node.
    /// According to the 
    let private synthesize_await (input : VisGraph * Node<nodePayload, edgePayload>) (rhs : TypedRhs) : (VisGraph * Node<nodePayload, edgePayload>) =
        // Extract.
        let graph = fst(input)
        let prevNode = snd(input)

        // New node and edge
        let newNode = graph.AddNode({label = ""; isComplex = IsSimple; isInitOrFinal = Neither})
        graph.AddEdge({label = renderRhsString rhs ; property = IsAwait}) prevNode newNode |> ignore

        (graph, newNode) 

    /// Synthesization of a single statement.
    let private synthesize_statement (stmt : Stmt) (graphAndPrevNode : VisGraph * Node<nodePayload, edgePayload>): VisGraph * Node<nodePayload, edgePayload> =
        match stmt with 
            | Await (_, typedRhs) -> synthesize_await (graphAndPrevNode) (typedRhs)
            // TODO
            //| ITE (range, typedRhs, stmtList, stmList)-> ()
            //| Cobegin (range, listOfStrengthAndStmts) -> ()
            //| WhileRepeat (range, typedRhs, stmtList) -> ()
            //| RepeatUntil (range, stmtList, typedRhs, bool) -> ()
            //| Preempt (range, preemeption, typedRhs, moment, stmtList) -> ()
            //| ActivityCall (range, qName, receiverOption, typedRhsList, typedLhsList) -> ()
            //| StmtSequence (stmtList) -> printf "loop this shit"
            | _ -> graphAndPrevNode // ignore all other statements and just return the construct as it was before.

    /// Synthesis of a multiple statements.
    let rec private synthesize_statements (stmts : Stmt list) (graphAndPrevNode : VisGraph * Node<nodePayload, edgePayload>): VisGraph * Node<nodePayload, edgePayload> =
        // Go over list and synthesize single statements until list is finished.
        match stmts with
            | head :: tail -> synthesize_statement head graphAndPrevNode |> synthesize_statements tail
            |  [] -> graphAndPrevNode     

    /// Synthesis of the body of an activity.
    let private synthesize_activity_body (stmts : Stmt list) : VisGraph =
        // Init.
        let graph = VisGraph.Empty()
        let init = graph.AddNode({label = ""; isComplex = IsSimple; isInitOrFinal = Init})
        let graphAndPrevNode = synthesize_statements stmts (graph, init)

        // Connect last available node to the final node. TODO only if available?
        let updatedGraph = fst(graphAndPrevNode)
        let final = updatedGraph.AddNode({label = ""; isComplex = IsSimple; isInitOrFinal = Final})
        updatedGraph.AddEdge ({label = "" ; property = IsImmediate}) (snd(graphAndPrevNode)) final |> ignore
        updatedGraph


    /// Synthesis of an activity.
    /// Gather data. 1 - name of activity, 2 - input and output data, 3 - construct activity body.
    let private synthesize_activity (entryPoint: SubProgramDecl) : Node<nodePayload, edgePayload> =     
        // Init Data.
        let name : string = entryPoint.name.ToString()

        let input1 = List.map paramToParam entryPoint.inputs
        let input2 = List.map extParamToParam entryPoint.globalInputs 
        let output1 = List.map paramToParam entryPoint.outputs 
        let output2 = List.map extParamToParam entryPoint.globalOutputsInScope 

        let iparam : BlechVisGraph.paramList = List.append (input1) (input2)
        let oparam : BlechVisGraph.paramList = List.append (output1) (output2) 

        let body = synthesize_activity_body entryPoint.body

        // Init Graph.
        let complexNode : complexOrSimple = IsComplex {body = body; isActivity = IsActivity {inputParams = iparam; outputParams = oparam}}
        Node<nodePayload, _>.Create({label = name; isComplex = complexNode; isInitOrFinal = Neither})


    /// Synthesis entry point. Pours the Blech code into a graph data modell (given by GenericGraph.fs).
    let private synthesize (entryPoint: SubProgramDecl) : (Node<nodePayload, edgePayload>) =
        // only synthesize if entry point is an actual activity and not a function.
        match entryPoint.isFunction with true -> failwith("Cannot visualize function.") | false -> synthesize_activity entryPoint


    /// Synthesis start. Has side effects: unkown.
    let startSynthesis (arg : Result<TypeCheckContext * BlechModule, Diagnostics.Logger>) = 

        // Access values.
        let resultTuple : TypeCheckContext*BlechModule = 
            match arg with 
            | Ok a -> a
            | Error b -> failwith("Can not visualize errorous code.")

        let blechModule : BlechModule = snd(resultTuple)
        match blechModule.entryPoint.IsNone with true -> failwith("Entry point needed for visualization.") | _ -> ()
        let entryPoint: SubProgramDecl = blechModule.entryPoint.Value  // this is the entry point for my synthesis, this is the outermost activity of interest.

        // synthesize this activity (recurseviley if needed).
        let activityNode = synthesize entryPoint
        
        // Optimizations take place here.
        // TODO.

        // Generate sctx content.
        let sctxString = SctxGenerator.generate activityNode

        // Print sctx content to a file.
        SctxToFile.putToFile sctxString