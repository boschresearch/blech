module Blech.Visualization.Visualization

    open Blech.Frontend
    open Blech.Frontend.BlechTypes
    open Blech.Common
    open Blech.Common.GenericGraph
    open Blech.Visualization.BlechVisGraph
    open Blech.Frontend.CommonTypes

    /// Unique id.
    let mutable bracketId = 0

    /// Filters a (input paramter) string, if it contains two curly brackets and is thus not wanted to be illustrated.
    let filterForCurlyBracketConstructions = fun s -> String.exists (fun c -> match c with '{' -> true | _ -> false) s && String.exists (fun c -> match c with '}' -> true | _ -> false) s

    /// Renders the string from the TypedRhs to a more presentable form. (E.g.: activity.in to in).
    /// Also checks in the end, if parameter is a {...}-construction, which is not wanted. Replaced by other string.
    // TODO improve this method. Converting from string to char[] and back on every method?
    let rec private renderRhsRhlString (rhsOrLhs : string) (original : string): string =
       let chars = Seq.toList rhsOrLhs

       match chars with 
            | head :: tail -> let stringTail = String.concat "" <| List.map string tail
                              match head with '.' -> renderRhsRhlString stringTail stringTail | _ -> renderRhsRhlString (stringTail) original
            | [] -> // Did not contain a dot. Now check for {...} construction.
                    bracketId <- bracketId + 1
                    match filterForCurlyBracketConstructions original with
                        | true -> "curlyBracket" + string bracketId
                        | false -> original // Did not contain a dot.

    /// Functions for transforming Blech paremters to my own parameter type.    
    let paramToParam = fun (paramDec : ParamDecl) -> {typeName = paramDec.datatype.ToString(); name = paramDec.name.basicId}
    let extParamToParam = fun (extVarDecl : ExternalVarDecl) -> {typeName = extVarDecl.datatype.ToString(); name = extVarDecl.name.basicId}

    /// Functions for transforming Rhs and Lhs paremters to my own strings.    
    let rhsToString = fun (rhs : TypedRhs) -> renderRhsRhlString (rhs.ToString()) (rhs.ToString())
    let lhsToString = fun (lhs : TypedLhs) -> renderRhsRhlString (lhs.ToString()) (lhs.ToString())

    /// Add an await statement to the graph connecting to the previous node. According to the proposal in the thesis.
    let private synthesize_await (graphBuilder : GraphBuilder) (rhs : TypedRhs) : GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder + 1

        // New node and edge
        let newNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount; wasVisualized = NotVisualized}
        graph.AddEdge {label = renderRhsRhlString (rhs.ToString()) (rhs.ToString()) ; property = IsAwait} prevNode newNode |> ignore

        (graph, newNode, stateCount, frth graphBuilder) 

    /// Add an if-else statement to the graph connecting to the previous node. According to the proposal in the thesis.
    // StateCount: If-Node +1, Else-Node +2, Closing-Node +3, if-Body +4 , Else-Body If-Body+1, Return Else-Body
    let rec private synthesize_ite (graphBuilder : GraphBuilder) (rhs : TypedRhs) (ifBlock : Stmt list) (elseBlock : Stmt list ): GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        // New node for each branch. Init their bodies and connect the nodes to the case-closing node. Else is only needed, if there are statements in the else-block. (TODO is this enough?)
        let ifBody = synthesize_complex_body ifBlock (stateCount + 4) (frth graphBuilder)

        let ifComplex : complexOrSimpleOrCobegin = IsComplex {body = frst3 ifBody ; isActivity = IsNotActivity}

        let ifNode = graph.AddNode {label = ""; isComplex = ifComplex; isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        graph.AddEdge {label = renderRhsRhlString (rhs.ToString()) (rhs.ToString()); property = IsConditional} prevNode ifNode |> ignore

        // TODO only connect if complex state has final state.
        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 3; wasVisualized = NotVisualized}
        graph.AddEdge {label = ""; property = IsTerminal} ifNode caseClosingNode |> ignore

        // Else-path gets a complex state, if the else block contains code.
        match elseBlock.Length with
            | 0 -> graph.AddEdge {label = "" ; property = IsImmediate} prevNode caseClosingNode |> ignore
                   (graph, caseClosingNode, scnd3 ifBody, thrd3 ifBody)
            | _ -> let elseBody = synthesize_complex_body elseBlock (scnd3 ifBody + 1) (thrd3 ifBody)
                   let elseComplex : complexOrSimpleOrCobegin = IsComplex {body = frst3 elseBody ; isActivity = IsNotActivity}
                   let elseNode = graph.AddNode {label = ""; isComplex = elseComplex; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}      
                   graph.AddEdge {label = "" ; property = IsImmediate} prevNode elseNode |> ignore
                   graph.AddEdge {label = "" ; property = IsTerminal} elseNode caseClosingNode |> ignore

                   (graph, caseClosingNode, scnd3 elseBody, thrd3 elseBody)


    /// Synthesize while statement.
    /// State Count: ComplexNode - statecount +1, Closing node: statecount + 2, Complex Body, statecount + 3, return count - complex body.
    and private synthesize_while_repeat (graphBuilder : GraphBuilder) (rhs : TypedRhs) (stmts : Stmt list) : GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        // TODO closing node only if there is a final node.
        let bodyOfLoop = synthesize_complex_body stmts (stateCount + 3) (frth graphBuilder)
        let complexNode = 
            graph.AddNode {label = ""; isComplex = IsComplex {body = frst3 bodyOfLoop ; isActivity = IsNotActivity}; isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        graph.AddEdge {label = renderRhsRhlString (rhs.ToString()) (rhs.ToString()); property = IsConditional} prevNode complexNode |> ignore
        graph.AddEdge {label = "" ; property = IsTerminal} complexNode prevNode |> ignore

        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}
        graph.AddEdge {label = ""; property = IsImmediate} prevNode caseClosingNode |> ignore

        (graph, caseClosingNode, scnd3 bodyOfLoop, thrd3 bodyOfLoop)

    /// Synthesize repeat statement.
    /// State Count: ComplexNode - statecount +1, Closing node: statecount + 2, Complex Body, statecount + 3, return count - complex body.
    /// TODO add that a loop can be endless
    and private synthesize_repeat_until (graphBuilder : GraphBuilder) (rhs : TypedRhs) (stmts : Stmt list) (isEndless : bool): GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        // TODO closing node only if there is a final node.
        let bodyOfLoop = synthesize_complex_body stmts (stateCount + 3) (frth graphBuilder)
        let complexNode = 
            graph.AddNode {label = ""; isComplex = IsComplex {body = frst3 bodyOfLoop ; isActivity = IsNotActivity}; isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}
        graph.AddEdge {label = "" ; property = IsImmediate} prevNode complexNode |> ignore
        // Add the edge to the previous node first.
        graph.AddEdge {label = renderRhsRhlString (rhs.ToString()) (rhs.ToString()); property = IsTerminal} complexNode caseClosingNode |> ignore
        graph.AddEdge {label = "" ; property = IsTerminal} complexNode complexNode |> ignore

        (graph, caseClosingNode, scnd3 bodyOfLoop, thrd3 bodyOfLoop)

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
        let bodyOfLoop = synthesize_complex_body stmts (stateCount + 3) (frth graphBuilder)
        let complexNode = 
            graph.AddNode {label = ""; isComplex = IsComplex {body = frst3 bodyOfLoop ; isActivity = IsNotActivity}; isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}
        
        // Determine the target node of the preemption.
        let abortTarget = match preemtpion with
                            | Abort -> caseClosingNode
                            | Reset -> complexNode
                            | Suspend -> failwith "Unreachable case."
        
        graph.AddEdge {label = "" ; property = IsImmediate} prevNode complexNode |> ignore
        graph.AddEdge {label = renderRhsRhlString (rhs.ToString()) (rhs.ToString()); property = IsAbort} complexNode abortTarget |> ignore
        graph.AddEdge {label = "" ; property = IsTerminal} complexNode caseClosingNode |> ignore

        (graph, caseClosingNode, scnd3 bodyOfLoop, thrd3 bodyOfLoop)

    /// Method that converts a single strength and statement to (Visgraph * Strength). Also returns the state count and the list of needed vars.
    and private convertSingleToCobeginPayload 
        (strengthsAndStmt : Strength * Stmt list) (stateCount : int) (neededVars : string list) : 
        (VisGraph * Strength * int * string list) =
        let result = synthesize_complex_body (snd strengthsAndStmt) stateCount neededVars
        (frst3 result, fst strengthsAndStmt, scnd3 result, thrd3 result)

    /// Method that converts a list of strength and statement lists to a cobegin payload. Returns the highest state count. And the list of needed variables.
    and private convertListToCobeginPayload 
        (strengthsAndStmts : (Strength * Stmt list) list) (stateCount : int) (accumulator : (VisGraph * Strength) list) (neededVars : string list) :
        ((VisGraph * Strength) list * int * string list)=
        match strengthsAndStmts with 
            | head :: tail -> let result = convertSingleToCobeginPayload head (stateCount + 1) neededVars
                              convertListToCobeginPayload tail (thrd result) ((frst result, scnd result) :: accumulator) (frth result)
            | [] -> (accumulator, stateCount, neededVars)

    /// Synthezises a cobegin construct.
    /// State Count: Complex State - statecount + 1, closing node - state count + 2, body of complex node state count + 3, and then + 1 on every branch added to the previous branch.
    and private synthesize_cobegin (graphBuilder : GraphBuilder) (strengthsAndStmts : (Strength * Stmt list) list) : GraphBuilder = 
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder
        
        // Construct branches, nodes and edges.
        let branches = convertListToCobeginPayload strengthsAndStmts (stateCount + 3) [] (frth graphBuilder)
        let complexNode = 
            graph.AddNode {label = ""; isComplex = IsCobegin( frst3 branches); isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}

        graph.AddEdge {label = "" ; property = IsImmediate} prevNode complexNode |> ignore
        graph.AddEdge {label = "" ; property = IsTerminal} complexNode caseClosingNode |> ignore

        (graph, caseClosingNode, scnd3 branches, thrd3 branches)

    /// Synthesizes a run statement. A node that references an activity.
    and private activity_called (graphBuilder : GraphBuilder) (actName : string) (typedRhsList : TypedRhs list) (typedLhsList: TypedLhs list): GraphBuilder = 
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder
        
        let inputList = List.map rhsToString typedRhsList
        let outputList = List.map lhsToString typedLhsList
        let neededVars = List.append (frth graphBuilder) (List.append inputList outputList)

        let cmplx = IsActivityCall(inputList, outputList)
        let complexNode = 
            graph.AddNode {label = actName; isComplex = cmplx ; isInitOrFinal = Neither; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        let caseClosingNode = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Neither; stateCount = stateCount + 2; wasVisualized = NotVisualized}

        graph.AddEdge {label = "" ; property = IsImmediate} prevNode complexNode |> ignore
        graph.AddEdge {label = "" ; property = IsTerminal} complexNode caseClosingNode |> ignore
        
        (graph, caseClosingNode, stateCount + 2, neededVars)

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
    /// Returns the body as graph as well as the highest state count for the internal behaviour. Needed for distinct identifiers. Also returns a list of need variables.
    and private synthesize_complex_body (stmts : Stmt list) (stateCount : int) (neededVars : string list) : VisGraph * int * string list =
        // Init.
        let graph = VisGraph.Empty()
        let init = graph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Init; stateCount = stateCount + 1; wasVisualized = NotVisualized}
        let graphBuilder = synthesize_statements stmts (graph, init, stateCount + 3, neededVars)

        // Connect last available node to the final node. TODO only if available?
        let updatedGraph = frst graphBuilder
        let final = updatedGraph.AddNode {label = ""; isComplex = IsSimple; isInitOrFinal = Final; stateCount = stateCount + 2; wasVisualized = NotVisualized}
        updatedGraph.AddEdge {label = "" ; property = IsImmediate} (scnd graphBuilder) final |> ignore
        (updatedGraph, thrd graphBuilder, frth graphBuilder)
   
    // Checks whether given variable is a member if the in- and output list. If yes, empty string is returned, if not, the variable name is returned.
    let rec private isVarInInAndOutput (inAndOutputVariables : paramList) (variable : string) : string =
        match inAndOutputVariables with 
            | head :: tail -> if head.name.Equals(variable) then "" else isVarInInAndOutput tail variable
            | [] -> variable

    /// Determines which of the given variables are local and needed by comparing given list to in- and output variables
    let rec private determineLocalVars (inAndOutputVariables : paramList) (neededVariables : string list) (accumulator : string list) : string list = 
        match neededVariables with
            | head :: tail ->   let result = isVarInInAndOutput inAndOutputVariables head
                                if result.Equals("") then determineLocalVars inAndOutputVariables tail accumulator else determineLocalVars inAndOutputVariables tail (result :: accumulator)
            | [] -> accumulator

    /// Synthesis of an activity.
    /// Returns the activity graph in a node, also returns the highest state count reached in the internal behaviour.
    let private synthesize_activity (entryPoint: SubProgramDecl) (stateCount : int): Node<nodePayload, edgePayload> * int =     
        // Init Data.
        let name : string = entryPoint.name.ToString()

        let iparam = List.map paramToParam entryPoint.inputs
        let oparam = List.map paramToParam entryPoint.outputs 

        let bodyStatecountAndVars = synthesize_complex_body entryPoint.body (stateCount + 1) []

        // Determine needed local variable (name)s, by comparing the needed variables given by analyzing the body and the given input and output parameters.
        let localVars = determineLocalVars (List.append iparam oparam) (thrd3 bodyStatecountAndVars) []

        // Init Graph.
        let complexNode : complexOrSimpleOrCobegin = IsComplex {body = frst3 bodyStatecountAndVars; isActivity = IsActivity {inputParams = iparam; outputParams = oparam; localVars = localVars}}
        (Node<nodePayload, _>.Create {label = name; isComplex = complexNode; isInitOrFinal = Neither ; stateCount = stateCount; wasVisualized = NotVisualized}, scnd3 bodyStatecountAndVars)


    /// Synthesis entry point. Pours the Blech code into a graph data modell (given by GenericGraph.fs).
    let rec private synthesize (programs: SubProgramDecl list) (accumulator : Node<nodePayload, edgePayload> list): (Node<nodePayload, edgePayload> list) =
        match programs with 
            | head :: tail -> match head.isFunction with
                                    | true -> synthesize tail accumulator // not visualising functions
                                    | false -> synthesize tail (fst (synthesize_activity head 0) :: accumulator)
            | [] -> accumulator

    /// Synthesis start. Has side effects: prints file to current folder.
    let startSynthesis (arg : Result<TypeCheckContext * BlechModule, Diagnostics.Logger>) (fileName : string )= 

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

        printfn "Found %i functions or activities." (blechModule.funacts.Length)

        // Synthesize the activities.
        let activityNodes : Node<nodePayload, edgePayload> list = synthesize blechModule.funacts []

        printfn "Synthesized %i activities." (activityNodes.Length)

        // Optimizations take place here.
        // TODO.

        // Generate sctx content.
        let sctxString = SctxGenerator.generate activityNodes

        // Print sctx content to a file.
        SctxToFile.putToFile sctxString fileName