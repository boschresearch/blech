module Blech.Visualization.Translation

    open Blech.Frontend.BlechTypes
    open Blech.Common
    open Blech.Common.GenericGraph
    open Blech.Visualization.BlechVisGraph
    open Blech.Frontend.CommonTypes

    // Default id for secondary state id.
    let private defaultSecondaryId = 0
    
    /// Checks a string from TypedRhs to a more presentable form.
    /// Identifies single words separated by round brackets and blanks and renders them.
    /// Special treatment of curly brackets.
    let rec renderRhsRhlString (toCheck : string) : string =
        let filterEmpty = fun s -> match s with "" -> false | _ -> true
        match toCheck.Contains '{' && toCheck.Contains '}' with
            | true ->   // Curly brackets cant be processed in sctx. Filter it out an let the core info be preserved through the label.
                        let separated = List.filter filterEmpty (Seq.toList (toCheck.Split([|'{';'}';' ';'=';','|])))
                        "struct" + String.concat "" separated
            | false ->  // Split on round and cornered brackets and blanks.
                        // This method will add an empty string if two separating delimeters follow directly after each other. Need to filter this out.
                        let separated = List.filter filterEmpty (Seq.toList (toCheck.Split([|'(';')';' ';'[';']'|])))
                        // Render single words.
                        let originalAndRenderedWords = List.map renderRhsRhlWordInitial separated
                        // Replace separated words in given string by their rendered counterparts.
                        let replaceOrigByRendered (acc:string) (pair:string*string) = acc.Replace(fst pair, snd pair)
                        List.fold replaceOrigByRendered toCheck originalAndRenderedWords

    /// Initially calls the render method. To be used in a list map so that both arguments are the same.
    /// Returns the original and the rendered ones as pairs.
    and private renderRhsRhlWordInitial(checkWord : string) : string * string =
        (checkWord, renderRhsRhlWord checkWord checkWord)

    /// Renders the single words of strings from the TypedRhs to a more presentable form. (E.g.: activity.in to in).
    /// Also checks in the end, if parameter is a {...}-construction, which is not wanted. Replaced by other string.
    // TODO improve this method. Converting from string to char[] and back on every method?
    and private renderRhsRhlWord (rhsOrLhs : string) (original : string): string =
       let chars = Seq.toList rhsOrLhs

       match chars with 
            | head :: tail -> let stringTail = String.concat "" <| List.map string tail
                              match head with '.' -> renderRhsRhlWord stringTail stringTail | _ -> renderRhsRhlWord (stringTail) original
            | [] -> original // Did not contain a dot.

    /// Functions for transforming Blech paremters to my own parameter type.    
    let paramToParam = fun (paramDec : ParamDecl) -> {TypeName = paramDec.datatype.ToString(); Name = paramDec.name.basicId}
    let extParamToParam = fun (extVarDecl : ExternalVarDecl) -> {TypeName = extVarDecl.datatype.ToString(); Name = extVarDecl.name.basicId}

    /// Functions for transforming Rhs and Lhs paremters to my own strings.    
    let rhsToString = fun (rhs : TypedRhs) -> renderRhsRhlString (rhs.ToString())
    let lhsToString = fun (lhs : TypedLhs) -> renderRhsRhlString (lhs.ToString())

    /// Updated the given node in the graph with the given information of the graphbuilder.
    let updateLabelOfNode (node:BlechNode) (gb:GraphBuilder) (graph:VisGraph) = graph.ReplacePayloadInByAndReturn node (node.Payload.SetLabel (returnLabel gb))

    /// Add an await statement to the graph connecting to the previous node. According to the proposal in the thesis.
    let private synthesizeAwait (graphBuilder : GraphBuilder) (rhs : TypedRhs) : GraphBuilder =
        // Extract.
        let graph = frst5 graphBuilder
        let prevNode = (scnd5 graphBuilder).Value
        let stateCount = thrd5 graphBuilder + 1

        // Update label of previous node.
        let updatedPrevNode = updateLabelOfNode prevNode graphBuilder graph

        // New node and edge.
        let newNode = graph.AddNode{Label = ""; 
                                    IsComplex = IsSimple; 
                                    IsInitOrFinal = NeitherInitOrFinal;
                                    StateCount = stateCount;
                                    SecondaryId = defaultSecondaryId;
                                    WasVisualized = NotVisualized; 
                                    WasHierarchyOptimized = NotHierarchyOptimized}
        graph.AddEdge {Label = renderRhsRhlString (rhs.ToString()); Property = IsAwait; WasOptimized = NotOptimized} updatedPrevNode newNode |> ignore

        (graph, Some newNode, stateCount, frth5 graphBuilder, None) 

    /// Add an if-else statement to the graph connecting to the previous node. According to the proposal in the thesis.
    // StateCount: If-Node +1, Else-Node +2, Closing-Node +3, if-Body +4 , Else-Body If-Body+1, Return Else-Body
    let rec private synthesizeIte (graphBuilder : GraphBuilder) (rhs : TypedRhs) (ifBlock : Stmt list) (elseBlock : Stmt list): GraphBuilder =
        // Extract.
        let graph = frst5 graphBuilder
        let prevNode = (scnd5 graphBuilder).Value
        let stateCount = thrd5 graphBuilder

        // New node for each branch. Init their bodies and connect the nodes to the case-closing node. 
        // Else is only needed, if there are statements in the else-block. (TODO is this enough?)
        let ifBody = synthesizeComplexBody ifBlock (stateCount + 4) (frth5 graphBuilder) (ffth5 graphBuilder)

        let caseClosingNode = graph.AddNode{Label = ""; 
                                            IsComplex = IsSimple; 
                                            IsInitOrFinal = NeitherInitOrFinal; 
                                            StateCount = stateCount + 3; 
                                            SecondaryId = defaultSecondaryId;
                                            WasVisualized = NotVisualized; 
                                            WasHierarchyOptimized = NotHierarchyOptimized}
        let ifComplex : ComplexOrSimpleOrCobegin = 
            IsComplex {Body = frst4 ifBody ; IsActivity = IsNotActivity; CaseClosingNode = {Opt = Some (findIds caseClosingNode)}; IsAbort = Neither}

        // TODO only connect if complex state has final state.
        let ifNode = graph.AddNode {Label = ""; 
                                    IsComplex = ifComplex; 
                                    IsInitOrFinal = NeitherInitOrFinal; 
                                    StateCount = stateCount + 1; 
                                    SecondaryId = defaultSecondaryId;
                                    WasVisualized = NotVisualized;
                                    WasHierarchyOptimized = NotHierarchyOptimized}
        graph.AddEdge {Label = renderRhsRhlString (rhs.ToString()); 
                       Property = IsConditional; 
                       WasOptimized = NotOptimized} 
                       prevNode ifNode |> ignore
        graph.AddEdge {Label = ""; Property = IsTerminal; WasOptimized = NotOptimized} ifNode caseClosingNode |> ignore

        // Else-path gets a complex state, if the else block contains code.
        match elseBlock.Length with
            | 0 -> graph.AddEdge {Label = "" ; Property = IsImmediate; WasOptimized = NotOptimized} prevNode caseClosingNode |> ignore
                   (graph, Some caseClosingNode, scnd4 ifBody, thrd4 ifBody, frth4 ifBody)
            | _ -> // Extract label, if present from if block statement list.
                   let elseBody = synthesizeComplexBody elseBlock (scnd4 ifBody + 1) (thrd4 ifBody) (ffth5 graphBuilder)
                   let elseComplex : ComplexOrSimpleOrCobegin = 
                        IsComplex {Body = frst4 elseBody ; IsActivity = IsNotActivity; CaseClosingNode = {Opt = Some (findIds caseClosingNode)}; IsAbort = Neither}
                   let elseNode = graph.AddNode{Label = ""; 
                                                IsComplex = elseComplex; 
                                                IsInitOrFinal = NeitherInitOrFinal; 
                                                StateCount = stateCount + 2; 
                                                SecondaryId = defaultSecondaryId;
                                                WasVisualized = NotVisualized;
                                                WasHierarchyOptimized = NotHierarchyOptimized}      
                   
                   graph.AddEdge {Label = " " ; Property = IsImmediate; WasOptimized = NotOptimized} prevNode elseNode |> ignore
                   graph.AddEdge {Label = "" ; Property = IsTerminal; WasOptimized = NotOptimized} elseNode caseClosingNode |> ignore

                   // Potential carry over labels from if- and else branch are merched.
                   let carryOverLabelIf = match frth4 ifBody with
                                            | Some label -> label + " "
                                            | None -> ""
                   let carryOverLabelElse = match frth4 elseBody with
                                                | Some label -> label
                                                | None -> ""
                   let carryOverLabel = match carryOverLabelIf + carryOverLabelElse with
                                            | "" -> None
                                            | _ -> Some (carryOverLabelIf + carryOverLabelElse)
                   (graph, Some caseClosingNode, scnd4 elseBody, thrd4 elseBody, carryOverLabel)

    /// Synthesize repeat statement.
    /// State Count: ComplexNode - statecount +1, Closing node: statecount + 2, Complex Body, statecount + 3, return count - complex body.
    and private synthesizeRepeatUntil (graphBuilder : GraphBuilder) (rhs : TypedRhs) (stmts : Stmt list) (isEndless : bool): GraphBuilder =
        //printfn "yea %b" isEndless
        // Extract.
        let graph = frst5 graphBuilder
        let prevNode = (scnd5 graphBuilder).Value
        let stateCount = thrd5 graphBuilder

        // Synthesize body.
        let bodyOfLoop = synthesizeComplexBody stmts (stateCount + 3) (frth5 graphBuilder) (ffth5 graphBuilder)

        // Is there a case closing node?
        // While true loops are transformed to isEndless = false repeats, with the condition "false".." || (renderRhsRhlString (rhs.ToString()) (rhs.ToString())).Equals "false"
        let caseClosingNodeMaybe = 
            match isEndless with
                | true -> None
                | false ->  let caseClosingNode = graph.AddNode {Label = "";
                                                                 IsComplex = IsSimple; 
                                                                 IsInitOrFinal = NeitherInitOrFinal; 
                                                                 StateCount = stateCount + 2;
                                                                 SecondaryId = defaultSecondaryId;
                                                                 WasVisualized = NotVisualized; 
                                                                 WasHierarchyOptimized = NotHierarchyOptimized}
                            Some caseClosingNode
        let caseClosingIdPair = match caseClosingNodeMaybe with
                                    | Some node -> {Opt = Some (findIds node)}
                                    | None -> {Opt = None}

        //Construct complex node based on calculated data.
        let complexNode = 
                graph.AddNode { Label = ""; 
                                IsComplex = 
                                    IsComplex {Body = frst4 bodyOfLoop ; IsActivity = IsNotActivity; CaseClosingNode = caseClosingIdPair; IsAbort = Neither};
                                IsInitOrFinal = NeitherInitOrFinal; 
                                StateCount = stateCount + 1;
                                SecondaryId = defaultSecondaryId; 
                                WasVisualized = NotVisualized; 
                                WasHierarchyOptimized = NotHierarchyOptimized}

        // Connect complex to case closing if available.
        if not isEndless then 
                graph.AddEdge {Label = renderRhsRhlString (rhs.ToString()); 
                               Property = IsConditionalTerminal; 
                               WasOptimized = NotOptimized} 
                               complexNode caseClosingNodeMaybe.Value |> ignore

        // Regular transitions that are always present
        graph.AddEdge {Label = "" ; Property = IsImmediate; WasOptimized = NotOptimized} prevNode complexNode |> ignore
        graph.AddEdge {Label = "" ; Property = IsTerminal; WasOptimized = NotOptimized} complexNode complexNode |> ignore

        (graph, caseClosingNodeMaybe, scnd4 bodyOfLoop, thrd4 bodyOfLoop, frth4 bodyOfLoop)

    /// Determines what a preemption depending on the type.
    /// State Count: ComplexNode - statecount +1, Closing node: statecount + 2, Complex Body, statecount + 3, return count - complex body + 1.
    and private synthesizePreempt (graphBuilder : GraphBuilder) (preemtpion : Preemption) (rhs : TypedRhs) (stmts : Stmt list) : GraphBuilder =
        match preemtpion with 
            | Suspend -> printfn "Caution suspend preemption not supported.";
            | _ -> () // Ok, do nothing.
        
        // Extract.
        let graph = frst5 graphBuilder
        let prevNode = (scnd5 graphBuilder).Value
        let stateCount = thrd5 graphBuilder

        // Determine the target node of the preemption.
        let abortLabel = renderRhsRhlString (rhs.ToString())
        let abortType = match preemtpion with
                            | Abort -> AbortWhen abortLabel
                            | Reset -> AbortRepeat abortLabel
                            | Suspend -> failwith "Unreachable case."

        // TODO closing node only if there is a final node.
        let bodyOfLoop = synthesizeComplexBody stmts (stateCount + 3) (frth5 graphBuilder) (ffth5 graphBuilder)
        let caseClosingNode = graph.AddNode{Label = ""; 
                                            IsComplex = IsSimple; 
                                            IsInitOrFinal = NeitherInitOrFinal; 
                                            StateCount = stateCount + 2;
                                            SecondaryId = defaultSecondaryId; 
                                            WasVisualized = NotVisualized; 
                                            WasHierarchyOptimized = NotHierarchyOptimized}
        let complexNode = graph.AddNode{Label = ""; 
                                        IsComplex = IsComplex {Body = frst4 bodyOfLoop; 
                                                               IsActivity = IsNotActivity; 
                                                               CaseClosingNode = {Opt = Some (findIds caseClosingNode)}; 
                                                               IsAbort = abortType};
                                        IsInitOrFinal = NeitherInitOrFinal; 
                                        StateCount = stateCount + 1;
                                        SecondaryId = defaultSecondaryId;
                                        WasVisualized = NotVisualized;
                                        WasHierarchyOptimized = NotHierarchyOptimized}
        
        // Determine the target node of the preemption.
        let abortTarget = match preemtpion with
                            | Abort -> caseClosingNode
                            | Reset -> complexNode
                            | Suspend -> failwith "Unreachable case."
        
        graph.AddEdge {Label = "" ; Property = IsImmediate; WasOptimized = NotOptimized} prevNode complexNode |> ignore
        graph.AddEdge {Label = abortLabel; Property = IsAbort; WasOptimized = NotOptimized} complexNode abortTarget |> ignore
        graph.AddEdge {Label = "" ; Property = IsTerminal; WasOptimized = NotOptimized} complexNode caseClosingNode |> ignore

        (graph, Some caseClosingNode, scnd4 bodyOfLoop, thrd4 bodyOfLoop, frth4 bodyOfLoop)

    /// Method that converts a single strength and statement to (Visgraph * Strength). Also returns the state count and the list of needed vars.
    /// Also carries over a potential label.
    and private convertSingleToCobeginPayload 
        (strengthsAndStmt : Strength * Stmt list) (stateCount : int) (neededVars : string list) (carryOverLabel : Option<string>): 
        (VisGraph * Strength * int * string list * Option<string>) =
        let result = synthesizeComplexBody (snd strengthsAndStmt) stateCount neededVars carryOverLabel
        (frst4 result, fst strengthsAndStmt, scnd4 result, thrd4 result, frth4 result)

    /// Method that converts a list of strength and statement lists to a cobegin payload, also keeps track of carryOverLabels from cobegin branches.
    /// Returns the highest state count. And the list of needed variables.
    and private convertListToCobeginPayload 
        (strengthsAndStmts : (Strength * Stmt list) list) (stateCount : int) 
        (accumulator : ((VisGraph * Strength) list) * Option<string>) (neededVars : string list) (carryOverLabel: Option<string>) :
        ((VisGraph * Strength) list * int * string list * Option<string>) =
        match strengthsAndStmts with 
            | head :: tail -> let result = convertSingleToCobeginPayload head (stateCount + 1) neededVars carryOverLabel
                              let carryOverLabelSingleCbgn = 
                                match ffth5 result with
                                            | Some label -> label + ""
                                            | None -> ""
                              // ACCUMULATOR MATCHEN              
                              let carryOverLabelCbgn = 
                                match snd accumulator with
                                            | Some label -> label
                                            | None -> ""
                              let carryOverAccumulator = 
                                match carryOverLabelSingleCbgn + carryOverLabelCbgn with 
                                            | "" -> None
                                            | _ -> Some (carryOverLabelSingleCbgn + carryOverLabelCbgn)    
                              let updatedAcc = ((frst5 result, scnd5 result) :: (fst accumulator), carryOverAccumulator)
                              convertListToCobeginPayload tail (thrd5 result) updatedAcc (frth5 result) carryOverLabel
            | [] -> (fst accumulator, stateCount, neededVars, snd accumulator) // Last string option now returns the accumulated label !!

    /// Synthezises a cobegin construct.
    /// State Count: Complex State - statecount + 1, closing node - state count + 2,
    /// body of complex node state count + 3, and then + 1 on every branch added to the previous branch.
    and private synthesizeCobegin (graphBuilder : GraphBuilder) (strengthsAndStmts : (Strength * Stmt list) list) : GraphBuilder = 
        // Extract.
        let graph = frst5 graphBuilder
        let prevNode = (scnd5 graphBuilder).Value
        let stateCount = thrd5 graphBuilder
        
        // Construct branches, nodes and edges.
        let branches = convertListToCobeginPayload strengthsAndStmts (stateCount + 3) ([], None) (frth5 graphBuilder) (ffth5 graphBuilder)
        let caseClosingNode = graph.AddNode{Label = ""; 
                                            IsComplex = IsSimple; 
                                            IsInitOrFinal = NeitherInitOrFinal; 
                                            StateCount = stateCount + 2;
                                            SecondaryId = defaultSecondaryId; 
                                            WasVisualized = NotVisualized; 
                                            WasHierarchyOptimized = NotHierarchyOptimized}
        let complexNode = graph.AddNode{Label = ""; 
                                        IsComplex = 
                                            IsCobegin{Content = frst4 branches; CaseClosingNode = {Opt = Some (findIds caseClosingNode)}}; 
                                        IsInitOrFinal = NeitherInitOrFinal;
                                        SecondaryId = defaultSecondaryId;
                                        StateCount = stateCount + 1; 
                                        WasVisualized = NotVisualized; 
                                        WasHierarchyOptimized = NotHierarchyOptimized}

        graph.AddEdge {Label = "" ; Property = IsImmediate; WasOptimized = NotOptimized} prevNode complexNode |> ignore
        graph.AddEdge {Label = "" ; Property = IsTerminal; WasOptimized = NotOptimized} complexNode caseClosingNode |> ignore

        (graph, Some caseClosingNode, scnd4 branches, thrd4 branches, frth4 branches)

    /// Synthesizes a run statement. A node that references an activity.
    and private activityCalled (graphBuilder : GraphBuilder) (actName : string) (typedRhsList : TypedRhs list) (typedLhsList: TypedLhs list): GraphBuilder = 
        // Extract.
        let graph = frst5 graphBuilder
        let prevNode = (scnd5 graphBuilder).Value
        let stateCount = thrd5 graphBuilder
        
        let inputList = List.map rhsToString typedRhsList
        let outputList = List.map lhsToString typedLhsList
        let neededVars = List.append (frth5 graphBuilder) (List.append inputList outputList)

        let cmplx = IsActivityCall{origName = actName; iovars = (inputList, outputList)}
        let complexNode = graph.AddNode{Label = actName; 
                                        IsComplex = cmplx ; 
                                        IsInitOrFinal = NeitherInitOrFinal; 
                                        StateCount = stateCount + 1;
                                        SecondaryId = defaultSecondaryId; 
                                        WasVisualized = NotVisualized; 
                                        WasHierarchyOptimized = NotHierarchyOptimized}
        let caseClosingNode = graph.AddNode{Label = ""; 
                                            IsComplex = IsSimple; 
                                            IsInitOrFinal = NeitherInitOrFinal; 
                                            StateCount = stateCount + 2;
                                            SecondaryId = defaultSecondaryId;
                                            WasVisualized = NotVisualized; 
                                            WasHierarchyOptimized = NotHierarchyOptimized}

        graph.AddEdge {Label = "" ; Property = IsImmediate; WasOptimized = NotOptimized} prevNode complexNode |> ignore
        graph.AddEdge {Label = "" ; Property = IsTerminal; WasOptimized = NotOptimized} complexNode caseClosingNode |> ignore
        
        (graph, Some caseClosingNode, stateCount + 2, neededVars, ffth5 graphBuilder)

    /// Synthesization of a single statement.
    and private synthesizeStatement (stmt : Stmt) (graphBuilder : GraphBuilder): GraphBuilder =
        match stmt with 
            | Await (_, typedRhs) -> synthesizeAwait graphBuilder typedRhs
            | ITE (_, typedRhs, ifStmts, elseStmts)-> synthesizeIte graphBuilder typedRhs ifStmts elseStmts
            //Unnötig, while is optimized in previous compiler steps. | WhileRepeat _ -> graphBuilder - synthesizeWhileRepeat graphBuilder typedRhs stmtList 
            | RepeatUntil (_, stmtList, typedRhs, bool) -> synthesizeRepeatUntil graphBuilder typedRhs stmtList bool
            | Preempt (_, preemeption, typedRhs, _, stmtList) -> synthesizePreempt graphBuilder preemeption typedRhs stmtList // TODO Argument 4 - Moment needed?
            | StmtSequence (stmtList) -> synthesizeStatements stmtList graphBuilder
            | Cobegin (_, listOfStrengthAndStmts) -> synthesizeCobegin graphBuilder listOfStrengthAndStmts
            | ActivityCall (_, qName, _, typedRhsList, typedLhsList) -> activityCalled graphBuilder (qName.ToString()) typedRhsList typedLhsList
            | StatementPragma stmtPragma -> attachToLabelOption graphBuilder (stmtPragma.GetLabel)
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
    /// Fourth return element is a potential carry over label.
    and private synthesizeComplexBody (stmts : Stmt list) (stateCount : int) (neededVars : string list) (carryOverLabel : Option<string>) 
        : VisGraph * int * string list * Option<string> =
        // Init.
        let graph = VisGraph.Empty()
        let init = graph.AddNode{Label = ""; 
                                IsComplex = IsSimple; 
                                IsInitOrFinal = InitNotFinal; 
                                StateCount = stateCount + 1;
                                SecondaryId = defaultSecondaryId; 
                                WasVisualized = NotVisualized; 
                                WasHierarchyOptimized = NotHierarchyOptimized}
        let graphBuilder = synthesizeStatements stmts (graph, Some init, stateCount + 3, neededVars, carryOverLabel)

        // Only add final node if previous statements resulted in a caseClosing node.
        let updatedGraph = match (scnd5 graphBuilder).IsSome with 
                            | true ->   let updatedGraph = frst5 graphBuilder
                                        let final = 
                                            updatedGraph.AddNode{
                                                Label = ""; 
                                                IsComplex = IsSimple; 
                                                IsInitOrFinal = FinalNotInit; 
                                                StateCount = stateCount + 2;
                                                SecondaryId = defaultSecondaryId;
                                                WasVisualized = NotVisualized; 
                                                WasHierarchyOptimized = NotHierarchyOptimized}
                                        updatedGraph.AddEdge {
                                            Label = ""; Property = IsImmediate; WasOptimized = NotOptimized} (scnd5 graphBuilder).Value final |> ignore
                                        updatedGraph
                            | false -> frst5 graphBuilder
        
        (updatedGraph, thrd5 graphBuilder, frth5 graphBuilder, ffth5 graphBuilder)
   
    // Checks whether given variable is a member if the in- and output list. If yes, empty string is returned, if not, the variable name is returned.
    let rec private isVarInInAndOutput (inAndOutputVariables : ParamList) (variable : string) : string =
        match inAndOutputVariables with 
            | head :: tail -> match head.Name.Equals(variable) with
                                | true -> ""
                                | false -> isVarInInAndOutput tail variable
            | [] -> variable

    /// Determines which of the given variables are local and needed by comparing given list to in- and output variables
    let rec private determineLocalVars (inAndOutputVariables : ParamList) (neededVariables : string list) (accumulator : string list) : string list = 
        match neededVariables with
            | head :: tail ->   let result = isVarInInAndOutput inAndOutputVariables head
                                match result with 
                                    | "" -> determineLocalVars inAndOutputVariables tail accumulator
                                    | _ -> determineLocalVars inAndOutputVariables tail (result :: accumulator)
            | [] -> accumulator

    /// Synthesis of an activity.
    /// Returns the activity graph in a node, also returns the highest state count reached in the internal behaviour.
    let private synthesizeActivity (entryPoint: SubProgramDecl) (stateCount : int): BlechNode * int =     
        // Init Data.
        let name : string = entryPoint.name.ToString()

        let iparam = List.map paramToParam entryPoint.inputs
        let oparam = List.map paramToParam entryPoint.outputs 

        let bodyStatecountAndVars = synthesizeComplexBody entryPoint.body (stateCount + 1) [] None

        // Determine needed local variable (name)s, by comparing the needed variables given by analyzing the body and the given input and output parameters.
        let localVars = determineLocalVars (List.append iparam oparam) (thrd4 bodyStatecountAndVars) []

        // Init Graph.
        let complexNode : ComplexOrSimpleOrCobegin = 
            IsComplex { Body = frst4 bodyStatecountAndVars; 
                        IsActivity = IsActivity {InputParams = iparam; OutputParams = oparam; LocalVars = localVars}; 
                        CaseClosingNode = {Opt = None}; IsAbort = Neither}
        (Node<NodePayload, _>.Create
            {Label = name; 
            IsComplex = complexNode; 
            IsInitOrFinal = NeitherInitOrFinal; 
            StateCount = stateCount;
            SecondaryId = defaultSecondaryId; 
            WasVisualized = NotVisualized;
            WasHierarchyOptimized = NotHierarchyOptimized},
            scnd4 bodyStatecountAndVars)

    /// Synthesis entry point. Pours the Blech code into a graph data modell (given by GenericGraph.fs).
    let rec synthesize (programs: SubProgramDecl list) (accumulator : BlechNode list): (BlechNode list) =
        match programs with 
            | head :: tail -> match head.isFunction with
                                    | true -> synthesize tail accumulator // not visualising functions
                                    | false -> synthesize tail (fst (synthesizeActivity head 0) :: accumulator)
            | [] -> accumulator