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

    /// Add an await statement to the graph connecting to the previous node. According to the proposal in the thesis.
    let private synthesize_await (graphBuilder : GraphBuilder) (rhs : TypedRhs) : GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder + 1

        // New node and edge
        let newNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount; wasVisualized = NotVisualized}
        graph.AddEdge {label = renderRhsString rhs ; property = IsAwait} prevNode newNode |> ignore

        (graph, newNode, stateCount) 

    /// Add an if-else statement to the graph connecting to the previous node. According to the proposal in the thesis.
    // StateCount: If-Node +1, Else-Node +2, Closing-Node +3, if-Body +4 , Else-Body If-Body+1, Return Else-Body
    let rec private synthesize_ite (graphBuilder : GraphBuilder) (rhs : TypedRhs) (ifBlock : Stmt list) (elseBlock : Stmt list ): GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        // New node for each branch. Init their bodies and connect the nodes to the case-closing node.
        let ifBody = synthesize_complex_body ifBlock (stateCount + 4)
        let elseBody = synthesize_complex_body elseBlock (snd ifBody + 1)

        let ifComplex : complexOrSimple = IsComplex {body = fst ifBody ; isActivity = IsNotActivity}
        let elseComplex : complexOrSimple = IsComplex {body = fst elseBody ; isActivity = IsNotActivity}

        let ifNode = graph.AddNode {label = ""; isComplex = ifComplex; isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        graph.AddEdge {label = renderRhsString rhs ; property = IsConditional} prevNode ifNode |> ignore

        let elseNode = graph.AddNode {label = ""; isComplex = elseComplex; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}      
        graph.AddEdge {label = "" ; property = IsImmediate} prevNode elseNode |> ignore

        // TODO only connect if complex state has final state.
        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 3; wasVisualized = NotVisualized}
        graph.AddEdge {label = ""; property = IsImmediate} ifNode caseClosingNode |> ignore
        graph.AddEdge {label = "" ; property = IsImmediate} elseNode caseClosingNode |> ignore

        (graph, caseClosingNode, snd elseBody)

    /// Synthesization of a single statement.
    /// TODO Labels for states.
    and private synthesize_statement (stmt : Stmt) (graphBuilder : GraphBuilder): GraphBuilder =
        match stmt with 
            | Await (_, typedRhs) -> synthesize_await graphBuilder typedRhs
            | ITE (_, typedRhs, ifStmts, elseStmts)-> synthesize_ite graphBuilder typedRhs ifStmts elseStmts
            // TODO 
            //| Cobegin (range, listOfStrengthAndStmts) -> ()
            //| WhileRepeat (range, typedRhs, stmtList) -> ()
            //| RepeatUntil (range, stmtList, typedRhs, bool) -> ()
            //| Preempt (range, preemeption, typedRhs, moment, stmtList) -> ()
            //| ActivityCall (range, qName, receiverOption, typedRhsList, typedLhsList) -> ()
            //| StmtSequence (stmtList) -> printf "loop this shit"
            | _ -> graphBuilder // ignore all other statements and just return the construct as it was before.

    /// Synthesis of a multiple statements.
    and private synthesize_statements (stmts : Stmt list) (graphBuilder : GraphBuilder): GraphBuilder =
        // Go over list and synthesize single statements until list is finished.
        match stmts with
            | head :: tail -> synthesize_statement head graphBuilder |> synthesize_statements tail 
            |  [] -> graphBuilder     

    /// Synthesis of the body of a complex node.
    /// State Count: +1 for Init, +2 for Final and +3 as Start for internal behaviour.
    /// Returns the body as graph as well as the highest state count for the internal behaviour. Needed for distinct identifiers.
    and private synthesize_complex_body (stmts : Stmt list) (stateCount : int): VisGraph * int =
        // Init.
        let graph = VisGraph.Empty()
        let init = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Init; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        let graphBuilder = synthesize_statements stmts (graph, init, stateCount + 3)

        // Connect last available node to the final node. TODO only if available?
        let updatedGraph = frst graphBuilder
        let final = updatedGraph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Final; stateCount = stateCount + 2; wasVisualized = NotVisualized}
        updatedGraph.AddEdge {label = "" ; property = IsImmediate} (scnd graphBuilder) final |> ignore
        (updatedGraph, thrd graphBuilder)

    /// Synthesis of an activity.
    /// Returns the activity graph in a node, also returns the highest state count reached in the internal behaviour.
    let private synthesize_activity (entryPoint: SubProgramDecl) (stateCount : int): Node<nodePayload, edgePayload> * int =     
        // Init Data.
        let name : string = entryPoint.name.ToString()

        let input1 = List.map paramToParam entryPoint.inputs
        let input2 = List.map extParamToParam entryPoint.globalInputs 
        let output1 = List.map paramToParam entryPoint.outputs 
        let output2 = List.map extParamToParam entryPoint.globalOutputsInScope 

        let iparam : BlechVisGraph.paramList = List.append input1 input2
        let oparam : BlechVisGraph.paramList = List.append output1 output2

        let body = synthesize_complex_body entryPoint.body (stateCount + 1)

        // Init Graph.
        let complexNode : complexOrSimple = IsComplex {body = fst body; isActivity = IsActivity {inputParams = iparam; outputParams = oparam}}
        (Node<nodePayload, _>.Create {label = name; isComplex = complexNode; isInitOrFinal = Neither ; stateCount = stateCount; wasVisualized = NotVisualized}, snd body)


    /// Synthesis entry point. Pours the Blech code into a graph data modell (given by GenericGraph.fs).
    let private synthesize (entryPoint: SubProgramDecl) : (Node<nodePayload, edgePayload>) =
        // only synthesize if entry point is an actual activity and not a function.
        match entryPoint.isFunction with true -> failwith("Cannot visualize function.") | false -> fst (synthesize_activity entryPoint 0)


    /// Synthesis start. Has side effects: unkown.
    let startSynthesis (arg : Result<TypeCheckContext * BlechModule, Diagnostics.Logger>) = 

        // Access values.
        let resultTuple : TypeCheckContext*BlechModule = 
            match arg with 
            | Ok a -> a
            | Error b -> failwith("Can not visualize errorous code.")

        let blechModule : BlechModule = snd resultTuple
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