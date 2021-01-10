 module Blech.Visualization.Translation

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
    let paramToParam = fun (paramDec : ParamDecl) -> {TypeName = paramDec.datatype.ToString(); Name = paramDec.name.basicId}
    let extParamToParam = fun (extVarDecl : ExternalVarDecl) -> {TypeName = extVarDecl.datatype.ToString(); Name = extVarDecl.name.basicId}

    /// Functions for transforming Rhs and Lhs paremters to my own strings.    
    let rhsToString = fun (rhs : TypedRhs) -> renderRhsRhlString (rhs.ToString()) (rhs.ToString())
    let lhsToString = fun (lhs : TypedLhs) -> renderRhsRhlString (lhs.ToString()) (lhs.ToString())

    /// Add an await statement to the graph connecting to the previous node. According to the proposal in the thesis.
    let private synthesizeAwait (graphBuilder : GraphBuilder) (rhs : TypedRhs) : GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder + 1

        // New node and edge
        let newNode = graph.AddNode {Label = ""; IsComplex = IsSimple; IsInitOrFinal = Neither; StateCount = stateCount; WasVisualized = NotVisualized}
        graph.AddEdge {Label = renderRhsRhlString (rhs.ToString()) (rhs.ToString()) ; Property = IsAwait} prevNode newNode |> ignore

        (graph, newNode, stateCount, frth graphBuilder) 

    /// Add an if-else statement to the graph connecting to the previous node. According to the proposal in the thesis.
    // StateCount: If-Node +1, Else-Node +2, Closing-Node +3, if-Body +4 , Else-Body If-Body+1, Return Else-Body
    let rec private synthesizeIte (graphBuilder : GraphBuilder) (rhs : TypedRhs) (ifBlock : Stmt list) (elseBlock : Stmt list ): GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        // New node for each branch. Init their bodies and connect the nodes to the case-closing node. Else is only needed, if there are statements in the else-block. (TODO is this enough?)
        let ifBody = synthesizeComplexBody ifBlock (stateCount + 4) (frth graphBuilder)

        let caseClosingNode = graph.AddNode {Label = ""; IsComplex = IsSimple; IsInitOrFinal = Neither; StateCount = stateCount + 3; WasVisualized = NotVisualized}
        let ifComplex : ComplexOrSimpleOrCobegin = IsComplex {Body = frst3 ifBody ; IsActivity = IsNotActivity; CaseClosingNode = Some caseClosingNode; IsAbort = IsAbort.Neither}

        // TODO only connect if complex state has final state.
        let ifNode = graph.AddNode {Label = ""; IsComplex = ifComplex; IsInitOrFinal = Neither; StateCount = stateCount + 1; WasVisualized = NotVisualized}
        graph.AddEdge {Label = renderRhsRhlString (rhs.ToString()) (rhs.ToString()); Property = IsConditional} prevNode ifNode |> ignore
        graph.AddEdge {Label = ""; Property = IsTerminal} ifNode caseClosingNode |> ignore

        // Else-path gets a complex state, if the else block contains code.
        match elseBlock.Length with
            | 0 -> graph.AddEdge {Label = "" ; Property = IsImmediate} prevNode caseClosingNode |> ignore
                   (graph, caseClosingNode, scnd3 ifBody, thrd3 ifBody)
            | _ -> let elseBody = synthesizeComplexBody elseBlock (scnd3 ifBody + 1) (thrd3 ifBody)
                   let elseComplex : ComplexOrSimpleOrCobegin = IsComplex {Body = frst3 elseBody ; IsActivity = IsNotActivity; CaseClosingNode = Some caseClosingNode; IsAbort = IsAbort.Neither}
                   let elseNode = graph.AddNode {Label = ""; IsComplex = elseComplex; IsInitOrFinal = Neither; StateCount = stateCount + 2; WasVisualized = NotVisualized}      
                   graph.AddEdge {Label = "" ; Property = IsImmediate} prevNode elseNode |> ignore
                   graph.AddEdge {Label = "" ; Property = IsTerminal} elseNode caseClosingNode |> ignore

                   (graph, caseClosingNode, scnd3 elseBody, thrd3 elseBody)


    /// Synthesize while statement.
    /// State Count: ComplexNode - statecount +1, Closing node: statecount + 2, Complex Body, statecount + 3, return count - complex body.
    and private synthesizeWhileRepeat (graphBuilder : GraphBuilder) (rhs : TypedRhs) (stmts : Stmt list) : GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        // TODO closing node only if there is a final node.
        let bodyOfLoop = synthesizeComplexBody stmts (stateCount + 3) (frth graphBuilder)
        let caseClosingNode = graph.AddNode {Label = ""; IsComplex = IsSimple; IsInitOrFinal = Neither; StateCount = stateCount + 2; WasVisualized = NotVisualized}
        let complexNode = 
            graph.AddNode {Label = ""; IsComplex = IsComplex {Body = frst3 bodyOfLoop ; IsActivity = IsNotActivity; CaseClosingNode = Some caseClosingNode; IsAbort = IsAbort.Neither}; IsInitOrFinal = Neither; StateCount = stateCount + 1; WasVisualized = NotVisualized}
        graph.AddEdge {Label = renderRhsRhlString (rhs.ToString()) (rhs.ToString()); Property = IsConditional} prevNode complexNode |> ignore
        graph.AddEdge {Label = "" ; Property = IsTerminal} complexNode prevNode |> ignore
        graph.AddEdge {Label = ""; Property = IsImmediate} prevNode caseClosingNode |> ignore

        (graph, caseClosingNode, scnd3 bodyOfLoop, thrd3 bodyOfLoop)

    /// Synthesize repeat statement.
    /// State Count: ComplexNode - statecount +1, Closing node: statecount + 2, Complex Body, statecount + 3, return count - complex body.
    /// TODO add that a loop can be endless
    and private synthesizeRepeatUntil (graphBuilder : GraphBuilder) (rhs : TypedRhs) (stmts : Stmt list) (isEndless : bool): GraphBuilder =
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        // TODO closing node only if there is a final node.
        let bodyOfLoop = synthesizeComplexBody stmts (stateCount + 3) (frth graphBuilder)
        let caseClosingNode = graph.AddNode {Label = ""; IsComplex = IsSimple; IsInitOrFinal = Neither; StateCount = stateCount + 2; WasVisualized = NotVisualized}
        let complexNode = 
            graph.AddNode {Label = ""; IsComplex = IsComplex {Body = frst3 bodyOfLoop ; IsActivity = IsNotActivity; CaseClosingNode = Some caseClosingNode; IsAbort = IsAbort.Neither}; IsInitOrFinal = Neither; StateCount = stateCount + 1; WasVisualized = NotVisualized}
        graph.AddEdge {Label = "" ; Property = IsImmediate} prevNode complexNode |> ignore
        // Add the edge to the previous node first.
        graph.AddEdge {Label = renderRhsRhlString (rhs.ToString()) (rhs.ToString()); Property = IsTerminal} complexNode caseClosingNode |> ignore
        graph.AddEdge {Label = "" ; Property = IsTerminal} complexNode complexNode |> ignore

        (graph, caseClosingNode, scnd3 bodyOfLoop, thrd3 bodyOfLoop)

    /// Determines what a preemption depending on the type.
    /// State Count: ComplexNode - statecount +1, Closing node: statecount + 2, Complex Body, statecount + 3, return count - complex body + 1.
    and private synthesizePreempt (graphBuilder : GraphBuilder) (preemtpion : Preemption) (rhs : TypedRhs) (stmts : Stmt list) : GraphBuilder =
        match preemtpion with 
            | Suspend -> printfn "Caution suspend preemption not supported.";
            | _ -> () // Ok, do nothing.
        
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder

        // Determine the target node of the preemption.
        let abortLabel = renderRhsRhlString (rhs.ToString()) (rhs.ToString())
        let abortType = match preemtpion with
                            | Abort -> AbortWhen abortLabel
                            | Reset -> AbortRepeat abortLabel
                            | Suspend -> failwith "Unreachable case."

        // TODO closing node only if there is a final node.
        let bodyOfLoop = synthesizeComplexBody stmts (stateCount + 3) (frth graphBuilder)
        let caseClosingNode = graph.AddNode {Label = ""; IsComplex = IsSimple; IsInitOrFinal = Neither; StateCount = stateCount + 2; WasVisualized = NotVisualized}
        let complexNode = 
            graph.AddNode {Label = ""; IsComplex = IsComplex {Body = frst3 bodyOfLoop ; IsActivity = IsNotActivity; CaseClosingNode = Some caseClosingNode; IsAbort = abortType}; IsInitOrFinal = Neither; StateCount = stateCount + 1; WasVisualized = NotVisualized}
        
        // Determine the target node of the preemption.
        let abortTarget = match preemtpion with
                            | Abort -> caseClosingNode
                            | Reset -> complexNode
                            | Suspend -> failwith "Unreachable case."
        
        graph.AddEdge {Label = "" ; Property = IsImmediate} prevNode complexNode |> ignore
        graph.AddEdge {Label = abortLabel; Property = IsAbort} complexNode abortTarget |> ignore
        graph.AddEdge {Label = "" ; Property = IsTerminal} complexNode caseClosingNode |> ignore

        (graph, caseClosingNode, scnd3 bodyOfLoop, thrd3 bodyOfLoop)

    /// Method that converts a single strength and statement to (Visgraph * Strength). Also returns the state count and the list of needed vars.
    and private convertSingleToCobeginPayload 
        (strengthsAndStmt : Strength * Stmt list) (stateCount : int) (neededVars : string list) : 
        (VisGraph * Strength * int * string list) =
        let result = synthesizeComplexBody (snd strengthsAndStmt) stateCount neededVars
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
    and private synthesizeCobegin (graphBuilder : GraphBuilder) (strengthsAndStmts : (Strength * Stmt list) list) : GraphBuilder = 
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder
        
        // Construct branches, nodes and edges.
        let branches = convertListToCobeginPayload strengthsAndStmts (stateCount + 3) [] (frth graphBuilder)
        let complexNode = 
            graph.AddNode {Label = ""; IsComplex = IsCobegin( frst3 branches); IsInitOrFinal = Neither; StateCount = stateCount + 1; WasVisualized = NotVisualized}
        let caseClosingNode = graph.AddNode {Label = ""; IsComplex = IsSimple; IsInitOrFinal = Neither; StateCount = stateCount + 2; WasVisualized = NotVisualized}

        graph.AddEdge {Label = "" ; Property = IsImmediate} prevNode complexNode |> ignore
        graph.AddEdge {Label = "" ; Property = IsTerminal} complexNode caseClosingNode |> ignore

        (graph, caseClosingNode, scnd3 branches, thrd3 branches)

    /// Synthesizes a run statement. A node that references an activity.
    and private activityCalled (graphBuilder : GraphBuilder) (actName : string) (typedRhsList : TypedRhs list) (typedLhsList: TypedLhs list): GraphBuilder = 
        // Extract.
        let graph = frst graphBuilder
        let prevNode = scnd graphBuilder
        let stateCount = thrd graphBuilder
        
        let inputList = List.map rhsToString typedRhsList
        let outputList = List.map lhsToString typedLhsList
        let neededVars = List.append (frth graphBuilder) (List.append inputList outputList)

        let cmplx = IsActivityCall(inputList, outputList)
        let complexNode = 
            graph.AddNode {Label = actName; IsComplex = cmplx ; IsInitOrFinal = Neither; StateCount = stateCount + 1; WasVisualized = NotVisualized}
        let caseClosingNode = graph.AddNode {Label = ""; IsComplex = IsSimple; IsInitOrFinal = Neither; StateCount = stateCount + 2; WasVisualized = NotVisualized}

        graph.AddEdge {Label = "" ; Property = IsImmediate} prevNode complexNode |> ignore
        graph.AddEdge {Label = "" ; Property = IsTerminal} complexNode caseClosingNode |> ignore
        
        (graph, caseClosingNode, stateCount + 2, neededVars)

    /// Synthesization of a single statement.
    /// TODO Labels for states.
    and private synthesizeStatement (stmt : Stmt) (graphBuilder : GraphBuilder): GraphBuilder =
        match stmt with 
            | Await (_, typedRhs) -> synthesizeAwait graphBuilder typedRhs
            | ITE (_, typedRhs, ifStmts, elseStmts)-> synthesizeIte graphBuilder typedRhs ifStmts elseStmts
            | WhileRepeat (_, typedRhs, stmtList) -> synthesizeWhileRepeat graphBuilder typedRhs stmtList // TODO entfernen, da unnötig?
            | RepeatUntil (_, stmtList, typedRhs, bool) -> synthesizeRepeatUntil graphBuilder typedRhs stmtList bool
            | Preempt (_, preemeption, typedRhs, _, stmtList) -> synthesizePreempt graphBuilder preemeption typedRhs stmtList // TODO Argument 4 - Moment needed?
            | StmtSequence (stmtList) -> synthesizeStatements stmtList graphBuilder
            | Cobegin (_, listOfStrengthAndStmts) -> synthesizeCobegin graphBuilder listOfStrengthAndStmts
            | ActivityCall (_, qName, _, typedRhsList, typedLhsList) -> activityCalled graphBuilder (qName.ToString()) typedRhsList typedLhsList
            | _ -> graphBuilder // ignore all other statements and just return the construct as it was before.

    /// Synthesis of a multiple statements.
    and private synthesizeStatements (stmts : Stmt list) (graphBuilder : GraphBuilder): GraphBuilder =
        // Go over list and synthesize single statements until list is finished.
        match stmts with
            | head :: tail -> synthesizeStatement head graphBuilder |> synthesizeStatements tail 
            |  [] -> graphBuilder     

    /// Synthesis of the body of a complex node.
    /// State Count: +1 for Init, +2 for Final and +3 as Start for internal behaviour.
    /// Returns the body as graph as well as the highest state count for the internal behaviour. Needed for distinct identifiers. Also returns a list of need variables.
    and private synthesizeComplexBody (stmts : Stmt list) (stateCount : int) (neededVars : string list) : VisGraph * int * string list =
        // Init.
        let graph = VisGraph.Empty()
        let init = graph.AddNode {Label = ""; IsComplex = IsSimple; IsInitOrFinal = Init; StateCount = stateCount + 1; WasVisualized = NotVisualized}
        let graphBuilder = synthesizeStatements stmts (graph, init, stateCount + 3, neededVars)

        // Connect last available node to the final node. TODO only if available?
        let updatedGraph = frst graphBuilder
        let final = updatedGraph.AddNode {Label = ""; IsComplex = IsSimple; IsInitOrFinal = Final; StateCount = stateCount + 2; WasVisualized = NotVisualized}
        updatedGraph.AddEdge {Label = ""; Property = IsImmediate} (scnd graphBuilder) final |> ignore
        (updatedGraph, thrd graphBuilder, frth graphBuilder)
   
    // Checks whether given variable is a member if the in- and output list. If yes, empty string is returned, if not, the variable name is returned.
    let rec private isVarInInAndOutput (inAndOutputVariables : ParamList) (variable : string) : string =
        match inAndOutputVariables with 
            | head :: tail -> if head.Name.Equals(variable) then "" else isVarInInAndOutput tail variable
            | [] -> variable

    /// Determines which of the given variables are local and needed by comparing given list to in- and output variables
    let rec private determineLocalVars (inAndOutputVariables : ParamList) (neededVariables : string list) (accumulator : string list) : string list = 
        match neededVariables with
            | head :: tail ->   let result = isVarInInAndOutput inAndOutputVariables head
                                if result.Equals("") then determineLocalVars inAndOutputVariables tail accumulator else determineLocalVars inAndOutputVariables tail (result :: accumulator)
            | [] -> accumulator

    /// Synthesis of an activity.
    /// Returns the activity graph in a node, also returns the highest state count reached in the internal behaviour.
    let private synthesizeActivity (entryPoint: SubProgramDecl) (stateCount : int): BlechNode * int =     
        // Init Data.
        let name : string = entryPoint.name.ToString()

        let iparam = List.map paramToParam entryPoint.inputs
        let oparam = List.map paramToParam entryPoint.outputs 

        let bodyStatecountAndVars = synthesizeComplexBody entryPoint.body (stateCount + 1) []

        // Determine needed local variable (name)s, by comparing the needed variables given by analyzing the body and the given input and output parameters.
        let localVars = determineLocalVars (List.append iparam oparam) (thrd3 bodyStatecountAndVars) []

        // Init Graph.
        let complexNode : ComplexOrSimpleOrCobegin = IsComplex {Body = frst3 bodyStatecountAndVars; IsActivity = IsActivity {InputParams = iparam; OutputParams = oparam; LocalVars = localVars}; CaseClosingNode = None; IsAbort = IsAbort.Neither}
        (Node<NodePayload, _>.Create {Label = name; IsComplex = complexNode; IsInitOrFinal = Neither ; StateCount = stateCount; WasVisualized = NotVisualized}, scnd3 bodyStatecountAndVars)


    /// Synthesis entry point. Pours the Blech code into a graph data modell (given by GenericGraph.fs).
    let rec synthesize (programs: SubProgramDecl list) (accumulator : BlechNode list): (BlechNode list) =
        match programs with 
            | head :: tail -> match head.isFunction with
                                    | true -> synthesize tail accumulator // not visualising functions
                                    | false -> synthesize tail (fst (synthesizeActivity head 0) :: accumulator)
            | [] -> accumulator