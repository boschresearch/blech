module Blech.Visualization.SctxGenerator

    open Blech.Common.GenericGraph
    open Blech.Visualization.BlechVisGraph
    open System.Collections.Generic
    open Blech.Frontend.CommonTypes

    //______________________________HELP METHODS & DATA_______________________________________________________ 
    /// Orders a list of edges to match the needed order in SCCharts. Strong aborts must always come first.
    /// Due to optimization steps, where edges from surrounding aborts are added, abort transitions can be present at the end of the list.
    /// Similar things go for conditional edges, they need to come before immediate transitions.
    /// This causes a compiler error in SCCharts.
    let rec orderEdgeList (edges : BlechEdge list) : BlechEdge list = 
        // 1. Extract all abort edges from list. 2. Put extracted elements at the beginning of the list.
        // In second step, but coniditonals in front.
        let partition = List.partition (fun e -> match e.Payload.Property with | IsAbort -> true | _ -> false) edges
        let sndPartition = List.partition (fun e -> match e.Payload.Property with | IsConditional | IsConditionalTerminal-> true | _ -> false) (snd partition)
        
        // Somewhere, the empty else conditionals get put before labelled conditionals in the opt. TODO find and eliminate so this will be unnecessary.
        let thrPartition = List.partition( fun e -> match e.Payload.Label with | "" -> false | _ ->  true) (fst sndPartition)
        // Somewhere in the optimization conditionals get inverted and  TODO find where and fix so this invertion coming next will be unnecessary.
        // Invert conditionals.
        let invertedConditionalsWithLabels = List.rev (fst thrPartition)
        //Combine.
        let conditionals = List.append invertedConditionalsWithLabels (snd thrPartition)

        // Aborts are the first element of the pair. Contitionals the first of the second pair.
        List.append (fst partition) (List.append conditionals (snd sndPartition))

    /// Constant for whitespaces.
    let private blank : string = " "

    /// Constant for line breaks.
    let private lnbreak : string = "\n"

    /// Concats string with commata to be used in a fold.
    let commaConcatination = fun acc elm -> acc + "," + elm

    /// List of Sccharts keywords that can not be used as identifiers for variables or acitivites or any other thing that is not a label.
    let scchartsKeywords =
        ["Pr";
         "_";
         "abort";
         "auto";
         "bool";
         "class";
         "clock";
         "combine";
         "commuting";
         "conflicting";
         "connector";
         "const";
         "dataflow";
         "deferred";
         "delayed";
         "do";
         "during";
         "else";
         "end";
         "entry";
         "exit";
         "expression";
         "extends";
         "extern";
         "fby";
         "final";
         "float";
         "for";
         "fork";
         "global";
         "go";
         "goto";
         "history";
         "host";
         "if";
         "immediate";
         "import";
         "initial";
         "input";
         "int";
         "is";
         "join";
         "json";
         "label";
         "max";
         "method";
         "min";
         "module";
         "nondeterministic";
         "none";
         "null";
         "once";
         "output";
         "override";
         "par";
         "pause";
         "period";
         "policy";
         "pre";
         "print";
         "private";
         "protected";
         "public";
         "pure";
         "random";
         "randomize";
         "ref";
         "region";
         "reset";
         "return";
         "run";
         "scchart";
         "schedule";
         "scope";
         "seq";
         "sfby";
         "shallow";
         "signal";
         "state";
         "static";
         "string";
         "strong";
         "struct";
         "suspend";
         "then";
         "to";
         "undefined";
         "val";
         "violation";
         "void";
         "weak";
         "while"
        ]

    /// Match .sctx keywords and replace them with an added underscore. Variables (in declaration and run statements) and activity names.
    let matchKeywords = fun (var:string) -> match List.contains var scchartsKeywords with 
                                                    | true -> "_"+var
                                                    | false -> var

    //______________________________SCTX GENERATION_______________________________________________________ 
    /// Converts a single param to a string.
    let private listParam (param : Param) (isInput : bool) : string =
        let inOrOut : string = 
            match isInput with
               | true -> "input"
               | false -> "output"

        // TODO anyone of these? Some sort of parsing. Pure signal problem might be due to name of the input/output.
        //output <- output + blank + inOrOut + blank + param.TypeName + blank + param.Name
        blank + inOrOut + " host \"" + param.TypeName + "\" " + matchKeywords param.Name + lnbreak            

    /// Method that converts a list of params to a string (sctx style).
    /// TODO convert to fold.
    let rec private listParams (paramList : ParamList) (isInput : bool): string =
        match paramList with 
            | head :: tail ->(listParam head isInput) + listParams tail isInput
            | [] -> ""
    
    /// Converts a single local variable to .sctx if its a variable name and not a primitive type.
    /// Decomposes complex boolean construct, e.g. x and not y into the local variables x and y.
    let private listLocalVar (var : string) : string list=
        /// Only list vars that are not primitive types. Ints, booleans, TODO doubles and other boolean constructs (and, or, not)
        match Seq.forall System.Char.IsDigit var || var.Equals("true") || var.Equals("false") || (var.Contains '{' && var.Contains '}') with
            | true -> [""]
            | false -> let blankSplit = Seq.toList (var.Split([|' '|])) // split into single words, then filter keywords 'and', 'or', 'not' out.
                       let expressionFiltered = List.filter (fun e -> not (e.Equals "not" || e.Equals "and" || e.Equals "or" || e.Equals "prev")) blankSplit
                       List.map (fun var -> "host \"localVar\" " + var + lnbreak) expressionFiltered

    /// Converts a list of local variables to a .sctx string. Filters duplicates.
    let rec private listLocalVars (vars : string list) : string = 
        List.collect listLocalVar vars |> List.distinct |> List.fold (+) ""

    /// Construct a string representing a single edge. Target is the combination of statecount and secondary id.
    let private singleEdge(edge : BlechEdge) (targetIds : string) (prio : int) : string =
        let prioLabel = string prio + ": "
        match edge.Payload.Property with 
            | IsAwait ->  "if true go to s" + string targetIds + " label \"" + edge.Payload.Label + "\"" + lnbreak
            | IsAbort -> "if true abort to s" + string targetIds + " label \"" + edge.Payload.Label + "\"" + lnbreak
            // Include prio.
            | IsTerminal -> "join to s" + string targetIds + " label \"" + prioLabel + edge.Payload.Label + "\"" + lnbreak
            | IsImmediate -> "immediate go to s" + string targetIds + " label \"" + prioLabel + edge.Payload.Label + "\"" + lnbreak
            | IsConditional ->  "immediate if true go to s" + string targetIds + " label \"" + prioLabel + edge.Payload.Label + "\"" + lnbreak
            | IsConditionalTerminal -> "immediate if true join to s" + string targetIds + " label \"" + prioLabel + edge.Payload.Label + "\"" + lnbreak

    /// Folding function that is used to fold a set of edges into their corresponding sctx strings.
    let rec foldEdges (accumulator : EdgeAccumulator) (edge : BlechEdge) : EdgeAccumulator =
        let currPrio = match edge.Payload.Property with 
                            | IsAwait | IsAbort -> thrd3 accumulator
                            | IsImmediate | IsTerminal | IsConditional | IsConditionalTerminal -> (thrd3 accumulator) + 1
        let singleEdgeString = singleEdge edge ((string edge.Target.Payload.StateCount) + (string edge.Target.Payload.SecondaryId)) currPrio

        // Only visualize node if it has not been visualized yet.
        let recursiveOnTargetNodes = 
            match edge.Target.Payload.WasVisualized with
                | Visualized -> "" // ok do not visualize this node.
                | NotVisualized -> addNodesAndEdges edge.Target

        (frst3 accumulator + singleEdgeString, scnd3 accumulator + recursiveOnTargetNodes, currPrio)

    /// Constructs the string for the edges and recursively calls the the illustration methods for the target nodes.
    and private addEdges (edges : HashSet<BlechEdge>) : string =
        // Accumulator is a triple consisting of (edgeStrings, recursiveNodeString, stateCount).
        // Accumulate the strings over the edges.
        let edgesAndRecursiveAccumulator = List.fold foldEdges ("","",0) (orderEdgeList (Seq.toList edges))

        // Put together the pieces and return ist.
        frst3 edgesAndRecursiveAccumulator + scnd3 edgesAndRecursiveAccumulator

    /// Transforms a single cobegin branch to a string.
    and private cobeginBranchToString (branch :  VisGraph * Strength) : string =
        let final = match snd branch with
                        | Strong -> ""
                        | Weak -> "final" + blank
        final + "region" + blank + "{" + lnbreak + bodyToSctx (fst branch) + lnbreak + "}"

    /// Iterates recursevily over cobegin branches and transforms them to a .sctx string.
    and private cobeginBranchesToString (branchList : (VisGraph * Strength) list) : string =
        match branchList with 
            | [head] -> cobeginBranchToString head
            | head :: tail -> cobeginBranchToString head + lnbreak + cobeginBranchesToString tail
            | [] -> ""

    /// Constructs a sctx string for an activity call.
    and private actCallToString (input : string list) (output : string list) (actName : string) : string =
        // Replace complex conditions containing boolean constructs (and, or, not).
        let workOnConditions = 
            fun (var:string) -> match Seq.forall System.Char.IsDigit var || var.Equals("true") || var.Equals("false") with
                                    | true -> var
                                    | false -> var.Replace("not", "!").Replace("or ", "||").Replace("or ", "&&")

        // Take care of "prev". Replace "prev " with "pre(" and concat a ")" and the end.
        let replacePrev = fun (var:string) -> match var.Contains "prev "with 
                                                | false -> var
                                                | true -> var.Replace("prev ", "pre(") + ")"
        
        // Apply both functions.
        let filteredAndCleaned = List.map (workOnConditions >> replacePrev >> matchKeywords) (List.append input output)
        let arguments = match filteredAndCleaned.Length with 
                        | 0 -> ""
                        | 1 -> "(" + List.head filteredAndCleaned + ")"
                        | _ -> "(" + List.fold commaConcatination (List.head filteredAndCleaned) (List.tail filteredAndCleaned) + ")"

        "is" + blank + actName + arguments        

    /// Adds nodes and edges recursively to a string, sctx conform. Returns a tuple where the first string is the sctx and the second string the state count.
    and private addNodesAndEdges (node : BlechNode) : string =
        // Add state, according to its settings (label, status) and mark node as visualized.
        let stateLabel : string = blank + "\"" + node.Payload.Label + "\""
        let initOrFinal : string = (match node.Payload.IsInitOrFinal.Init with | IsInit -> blank + "initial" | IsNotInit -> "") +
                                   (match node.Payload.IsInitOrFinal.Final with | IsFinal -> blank + "final" | IsNotFinal -> "")
        let isConnector : string = match node.Payload.IsComplex with
                                        | IsConnector -> " connector"
                                        | _ -> ""      

        let stateString = blank + initOrFinal + isConnector + " state s" + string node.Payload.StateCount + string node.Payload.SecondaryId + stateLabel 
        node.Payload.Visualize

        // Hierarchical states. Check if it is hierarchical, then match for regular body or activity.
        let complexState : string = match node.Payload.IsComplex with
                                        | IsComplex cmplx -> match cmplx.IsActivity with 
                                                                | IsActivity _ -> "{"  + lnbreak + activityToSctx node.Payload  + lnbreak + "}" + lnbreak
                                                                | IsNotActivity -> "{"  + lnbreak + bodyToSctx cmplx.Body  + lnbreak + "}" + lnbreak
                                        | IsSimple | IsConnector -> "" // Ok. Do nothing.
                                        | IsCobegin cbgn-> "{" + lnbreak + cobeginBranchesToString cbgn.Content + lnbreak + "}" + lnbreak
                                        | IsActivityCall actCall -> actCallToString actCall.GetIns actCall.GetOuts node.Payload.Label
        
        // If the node is a final node, we are finished, as there are no subsequent nodes.
        let edgeStringsAndRecursiveNodes =  match node.Payload.IsInitOrFinal.Final with
                                                | IsFinal -> ""
                                                | _ ->  // Add and illustrate edges. Calls method recursively to add the target states and their subsequent edges.
                                                        addEdges node.Outgoing

        stateString + blank + complexState + blank + edgeStringsAndRecursiveNodes

    /// Converts the body of an activity (or any other complex state) to a sctx-conform string.
    and private bodyToSctx (body : BlechVisGraph.VisGraph) : string =
        // Find init node.
        let initNode = findInitNodeInHashSet body.Nodes
        // Add nodes and edges recursively. 
        addNodesAndEdges initNode

    /// Generates the sctx for an activity. Returns a string for this particular activity. Might be called recursively. Hence, it is its own method.
    and private activityToSctx (activityNode : NodePayload) : string = 
        // Safety assert. Init with empty Payload.
        let complexNode = match(activityNode.IsComplex) with
                            | IsComplex a -> a
                            | _ -> failwith("Can not continue, expected an activity.")
                            
        let activityProps = match(complexNode.IsActivity) with
                            | IsActivity a -> a
                            | IsNotActivity -> failwith("Can not continue. Expected an activity.")

        // Construct the resulting string..
        "scchart" + blank + activityNode.Label + blank
                  + "{" + lnbreak
                  + listParams activityProps.InputParams true
                  + listParams activityProps.OutputParams false
                  + listLocalVars activityProps.LocalVars
                  + bodyToSctx complexNode.Body
                  + "}" + lnbreak + lnbreak

    /// Generate sctx file content.
    let rec generate (activities : BlechNode list) : string =
        // Generates activities one by one and concats the single strings together.
        // TODO We need to add variables in the beginning. Right now working with conditions as labels. In "if elses", we lose the information which comes first.
        match activities with 
            | head :: tail -> activityToSctx head.Payload + generate tail
            | [] -> ""