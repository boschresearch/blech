module Blech.Visualization.Visualization

    open Blech.Frontend
    open Blech.Frontend.BlechTypes
    open Blech.Common
    open Blech.Common.GenericGraph
    open Blech.Visualization.BlechVisGraph
    open Blech.Frontend.CommonTypes

    /// Renders the string from the TypedRhs to a more presentable form. (E.g.: activity.in to in).
    // TODO improve this method. Converting from string to char[] and back on every method?
    let rec private renderRhsRhlString (rhsOrLhs : string) : string =
       let chars = Seq.toList rhsOrLhs

       match chars with 
            | head :: tail -> let stringTail = String.concat "" <| List.map string tail
                              match head with '.' -> stringTail | _ -> renderRhsRhlString (stringTail)
            | [] -> failwith "Unexpected error parsing a RHS or LHS string." // TODO this should not happen.

    /// Functions for transforming Blech paremters to my own parameter type.    
    let paramToParam = fun (paramDec : ParamDecl) -> {typeName = paramDec.datatype.ToString(); name = paramDec.name.basicId}
    let extParamToParam = fun (extVarDecl : ExternalVarDecl) -> {typeName = extVarDecl.datatype.ToString(); name = extVarDecl.name.basicId}

    /// Functions for transforming Rhs and Lhs paremters to my own strings.    
    let rhsToString = fun (rhs : TypedRhs) -> renderRhsRhlString (rhs.ToString())
    let lhsToString = fun (lhs : TypedLhs) -> renderRhsRhlString (lhs.ToString())

    /// Add an await statement to the graph connecting to the previous node. According to the proposal in the thesis.
    let private synthesize_await (graphBuilder : GraphBuilder) (rhs : TypedRhs) : GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder + 1

        // New node and edge
        let newNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount; wasVisualized = NotVisualized}
        graph.AddEdge {label = renderRhsRhlString (rhs.ToString()) ; property = IsAwait} prevNode newNode |> ignore

        (graph, newNode, stateCount) 

    /// Add an if-else statement to the graph connecting to the previous node. According to the proposal in the thesis.
    // StateCount: If-Node +1, Else-Node +2, Closing-Node +3, if-Body +4 , Else-Body If-Body+1, Return Else-Body
    let rec private synthesize_ite (graphBuilder : GraphBuilder) (rhs : TypedRhs) (ifBlock : Stmt list) (elseBlock : Stmt list ): GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        // New node for each branch. Init their bodies and connect the nodes to the case-closing node. Else is only needed, if there are statements in the else-block. (TODO is this enough?)
        let ifBody = synthesize_complex_body ifBlock (stateCount + 4)

        let ifComplex : complexOrSimpleOrCobegin = IsComplex {body = fst ifBody ; isActivity = IsNotActivity}

        let ifNode = graph.AddNode {label = ""; isComplex = ifComplex; isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        graph.AddEdge {label = renderRhsRhlString (rhs.ToString()) ; property = IsConditional} prevNode ifNode |> ignore

        // TODO only connect if complex state has final state.
        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 3; wasVisualized = NotVisualized}
        graph.AddEdge {label = ""; property = IsTerminal} ifNode caseClosingNode |> ignore

        // Else-path gets a complex state, if the else block contains code.
        match elseBlock.Length with
            | 0 -> graph.AddEdge {label = "" ; property = IsImmediate} prevNode caseClosingNode |> ignore
                   (graph, caseClosingNode, snd ifBody)
            | _ -> let elseBody = synthesize_complex_body elseBlock (snd ifBody + 1)
                   let elseComplex : complexOrSimpleOrCobegin = IsComplex {body = fst elseBody ; isActivity = IsNotActivity}
                   let elseNode = graph.AddNode {label = ""; isComplex = elseComplex; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}      
                   graph.AddEdge {label = "" ; property = IsImmediate} prevNode elseNode |> ignore
                   graph.AddEdge {label = "" ; property = IsTerminal} elseNode caseClosingNode |> ignore

                   (graph, caseClosingNode, snd elseBody)


    /// Synthesize while statement.
    /// State Count: ComplexNode - statecount +1, Closing node: statecount + 2, Complex Body, statecount + 3, return count - complex body.
    and private synthesize_while_repeat (graphBuilder : GraphBuilder) (rhs : TypedRhs) (stmts : Stmt list) : GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        // TODO closing node only if there is a final node.
        let bodyOfLoop = synthesize_complex_body stmts (stateCount + 3)
        let complexNode = 
            graph.AddNode {label = ""; isComplex = IsComplex {body = fst bodyOfLoop ; isActivity = IsNotActivity}; isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        graph.AddEdge {label = renderRhsRhlString (rhs.ToString()) ; property = IsConditional} prevNode complexNode |> ignore
        graph.AddEdge {label = "" ; property = IsTerminal} complexNode prevNode |> ignore

        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}
        graph.AddEdge {label = ""; property = IsImmediate} prevNode caseClosingNode |> ignore

        (graph, caseClosingNode, snd bodyOfLoop)

    /// Synthesize repeat statement.
    /// State Count: ComplexNode - statecount +1, Closing node: statecount + 2, Complex Body, statecount + 3, return count - complex body.
    /// TODO add that a loop can be endless
    and private synthesize_repeat_until (graphBuilder : GraphBuilder) (rhs : TypedRhs) (stmts : Stmt list) (isEndless : bool): GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        // TODO closing node only if there is a final node.
        let bodyOfLoop = synthesize_complex_body stmts (stateCount + 3)
        let complexNode = 
            graph.AddNode {label = ""; isComplex = IsComplex {body = fst bodyOfLoop ; isActivity = IsNotActivity}; isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}
        graph.AddEdge {label = "" ; property = IsImmediate} prevNode complexNode |> ignore
        // Add the edge to the previous node first.
        graph.AddEdge {label = renderRhsRhlString (rhs.ToString()); property = IsTerminal} complexNode caseClosingNode |> ignore
        graph.AddEdge {label = "" ; property = IsTerminal} complexNode complexNode |> ignore

        (graph, caseClosingNode, snd bodyOfLoop)

    /// Determines what a preemption depending on the type.
    /// State Count: ComplexNode - statecount +1, Closing node: statecount + 2, Complex Body, statecount + 3, return count - complex body + 1.
    and private synthesize_preempt (graphBuilder : GraphBuilder) (preemtpion : Preemption) (rhs : TypedRhs) (stmts : Stmt list) : GraphBuilder =
        match preemtpion with 
            | Suspend -> printfn "Caution suspend preemption not supported.";
            | _ -> () // Ok, do nothing.
        
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        // TODO closing node only if there is a final node.
        let bodyOfLoop = synthesize_complex_body stmts (stateCount + 3)
        let complexNode = 
            graph.AddNode {label = ""; isComplex = IsComplex {body = fst bodyOfLoop ; isActivity = IsNotActivity}; isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}
        
        // Determine the target node of the preemption.
        let abortTarget = match preemtpion with
                            | Abort -> caseClosingNode
                            | Reset -> complexNode
                            | Suspend -> failwith "Unreachable case."
        
        graph.AddEdge {label = "" ; property = IsImmediate} prevNode complexNode |> ignore
        graph.AddEdge {label = renderRhsRhlString (rhs.ToString()); property = IsAbort} complexNode abortTarget |> ignore
        graph.AddEdge {label = "" ; property = IsTerminal} complexNode caseClosingNode |> ignore

        (graph, caseClosingNode, snd bodyOfLoop)

    /// Method that converts a single strength and statement to (Visgraph * Strength). Also returns the state count.
    and private convertSingleToCobeginPayload (strengthsAndStmt : Strength * Stmt list) (stateCount : int) : (VisGraph * Strength * int) =
        let result = synthesize_complex_body (snd strengthsAndStmt) stateCount
        (fst result, fst strengthsAndStmt, snd result)

    /// Method that converts a list of strength and statement lists to a cobegin payload. Returns the highest state count.
    and private convertListToCobeginPayload (strengthsAndStmts : (Strength * Stmt list) list) (stateCount : int) (accumulator : (VisGraph * Strength) list) : ((VisGraph * Strength) list * int)=
        match strengthsAndStmts with 
            | head :: tail -> let result = convertSingleToCobeginPayload head (stateCount + 1)
                              convertListToCobeginPayload tail (thrd result) ((frst result, scnd result) :: accumulator)
            | [] -> (accumulator, stateCount)

    /// Synthezises a cobegin construct.
    /// State Count: Complex State - statecount + 1, closing node - state count + 2, body of complex node state count + 3, and then + 1 on every branch added to the previous branch.
    and private synthesize_cobegin (graphBuilder : GraphBuilder) (strengthsAndStmts : (Strength * Stmt list) list) : GraphBuilder = 
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder
        
        // Construct branches, nodes and edges.
        let branches = convertListToCobeginPayload strengthsAndStmts (stateCount + 3) []
        let complexNode = 
            graph.AddNode {label = ""; isComplex = IsCobegin( fst branches); isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}

        graph.AddEdge {label = "" ; property = IsImmediate} prevNode complexNode |> ignore
        graph.AddEdge {label = "" ; property = IsTerminal} complexNode caseClosingNode |> ignore

        (graph, caseClosingNode, snd branches)

    /// Synthesizes a run statement. A node that references an activity.
    and private activity_called (graphBuilder : GraphBuilder) (actName : string) (typedRhsList : TypedRhs list) (typedLhsList: TypedLhs list): GraphBuilder = 
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        let inputs = List.map paramToParam
        
        let cmplx = IsActivityCall(List.map rhsToString typedRhsList, List.map lhsToString typedLhsList)
        let complexNode = 
            graph.AddNode {label = actName; isComplex = cmplx ; isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}

        graph.AddEdge {label = "" ; property = IsImmediate} prevNode complexNode |> ignore
        graph.AddEdge {label = "" ; property = IsTerminal} complexNode caseClosingNode |> ignore
        
        (graph, caseClosingNode, stateCount + 2)

    /// Synthesization of a single statement.
    /// TODO Labels for states.
    and private synthesize_statement (stmt : Stmt) (graphBuilder : GraphBuilder): GraphBuilder =
        match stmt with 
            | Await (_, typedRhs) -> synthesize_await graphBuilder typedRhs
            | ITE (_, typedRhs, ifStmts, elseStmts)-> synthesize_ite graphBuilder typedRhs ifStmts elseStmts
            | WhileRepeat (_, typedRhs, stmtList) -> synthesize_while_repeat graphBuilder typedRhs stmtList // TODO entfernen, da unnötig?
            | RepeatUntil (_, stmtList, typedRhs, bool) -> synthesize_repeat_until graphBuilder typedRhs stmtList bool
            | Preempt (_, preemeption, typedRhs, _, stmtList) -> synthesize_preempt graphBuilder preemeption typedRhs stmtList // TODO Argument 4 - Moment needed?
            | StmtSequence (stmtList) -> synthesize_statements stmtList graphBuilder
            | Cobegin (_, listOfStrengthAndStmts) -> synthesize_cobegin graphBuilder listOfStrengthAndStmts
            | ActivityCall (_, qName, _, typedRhsList, typedLhsList) -> activity_called graphBuilder (qName.ToString()) typedRhsList typedLhsList
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
        let complexNode : complexOrSimpleOrCobegin = IsComplex {body = fst body; isActivity = IsActivity {inputParams = iparam; outputParams = oparam}}
        (Node<nodePayload, _>.Create {label = name; isComplex = complexNode; isInitOrFinal = Neither ; stateCount = stateCount; wasVisualized = NotVisualized}, snd body)


    /// Synthesis entry point. Pours the Blech code into a graph data modell (given by GenericGraph.fs).
    let rec private synthesize (programs: SubProgramDecl list) (accumulator : Node<nodePayload, edgePayload> list): (Node<nodePayload, edgePayload> list) =
        match programs with 
            | head :: tail -> match head.isFunction with
                                    | true -> accumulator // not visualising functions
                                    | false -> synthesize tail (fst (synthesize_activity head 0) :: accumulator)
            | [] -> accumulator

    /// Synthesis start. Has side effects: unkown.
    let startSynthesis (arg : Result<TypeCheckContext * BlechModule, Diagnostics.Logger>) = 

        // Access values.
        let resultTuple : TypeCheckContext*BlechModule = 
            match arg with 
            | Ok a -> a
            | Error b -> failwith("Can not visualize errorous code: " + b.ToString())

        let blechModule : BlechModule = snd resultTuple
        // TODO Rolle des Entry Points klären.
        //match blechModule.entryPoint.IsNone with true -> failwith("Entry point needed for visualization.") | _ -> () // TODO is it really needed?
        //let entryPoint: SubProgramDecl = blechModule.entryPoint.Value  // this is the entry point for my synthesis, this is the outermost activity of interest.
        //let otherActivitiesAndFunctions: SubProgramDecl list = blechModule.funacts
        //let allActivitiesAndFunctions = entryPoint :: otherActivitiesAndFunctions
        // let activityNodes : Node<nodePayload, edgePayload> list = synthesize allActivitiesAndFunctions []

        // Synthesize the activities.
        let activityNodes : Node<nodePayload, edgePayload> list = synthesize blechModule.funacts []

        // Optimizations take place here.
        // TODO.

        // Generate sctx content.
        let sctxString = SctxGenerator.generate activityNodes

        // Print sctx content to a file.
        SctxToFile.putToFile sctxString