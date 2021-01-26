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
        let partition = List.partition (fun e -> match e.Payload.Property with | IsAbort -> true | _ -> false) edges
        let sndPartition = List.partition (fun e -> match e.Payload.Property with | IsConditional -> true | _ -> false) (snd partition)
        
        // Aborts are the first element of the pair. Contitionals the first of the second pair.
        List.append (fst partition) (List.append (fst sndPartition) (snd sndPartition))

    /// Constant for whitespaces.
    let private blank : string = " "

    /// Constant for line breaks.
    let private lnbreak : string = "\n"

    /// Concats string with commata to be used in a fold.
    let commaConcatination = fun elm acc -> acc + "," + elm

    //______________________________SCTX GENERATION_______________________________________________________ 
    /// Converts a single param to a string.
    let private listParam (param : Param) (isInput : bool) : string =
        let inOrOut : string = 
            match isInput with
               | true -> "input"
               | false -> "output"

        // TODO anyone of these? Some sort of parsing. Pure signal problem might be due to name of the input/output.
        //output <- output + blank + inOrOut + blank + param.TypeName + blank + param.Name
        blank + inOrOut + " host \"" + param.TypeName + "\" " + param.Name + lnbreak            

    /// Method that converts a list of params to a string (sctx style).
    let rec private listParams (paramList : ParamList) (isInput : bool): string =
        match paramList with 
            | head :: tail ->(listParam head isInput) + listParams tail isInput
            | [] -> ""
    
    /// Converts a single local variable to .sctx if it a variable name and not a primitive type.
    let private listLocalVar (var : string) : string =
        /// Only list vars that are not primitive types. Ints, booleans and TODO doubles.
        match Seq.forall System.Char.IsDigit var || var.Equals("true") || var.Equals("false") with
            | true -> ""
            | false -> "host \"localVar\" " + var + lnbreak

    /// Converts a list of local variables to a .sctx string.
    let rec private listLocalVars (vars : string list ) : string = 
        match vars with
            | head :: tail -> listLocalVar head + listLocalVars tail
            | [] -> ""

    /// Construct a string representing a single edge.
    let private singleEdge(edge : BlechEdge) (target : int): string =
        match edge.Payload.Property with 
            | IsAwait ->  "if true go to s" + string target + " label \"" + edge.Payload.Label + "\"" + lnbreak
            | IsConditional ->  "immediate if true go to s" + string target + " label \"" + edge.Payload.Label + "\"" + lnbreak
            | IsImmediate -> "immediate go to s" + string target + " label \"" + edge.Payload.Label + "\"" + lnbreak
            | IsAbort -> "if true abort to s" + string target + " label \"" + edge.Payload.Label + "\"" + lnbreak
            | IsTerminal -> "join to s" + string target + " label \"" + edge.Payload.Label + "\"" + lnbreak
            | IsConditionalTerminal -> "immediate if true join to s" + string target + " label \"" + edge.Payload.Label + "\"" + lnbreak

    /// Folding function that is used to fold a set of edges into their corresponding sctx strings.
    let rec foldEdges (accumulator : EdgeAccumulator) (edge : BlechEdge) : EdgeAccumulator =
        let singleEdgeString = singleEdge edge edge.Target.Payload.StateCount

        // Only visualize node if it has not been visualized yet.
        let recursiveOnTargetNodes = 
            match edge.Target.Payload.WasVisualized with
                | Visualized -> "" // ok do not visualize this node.
                | NotVisualized ->  addNodesAndEdges edge.Target

        (fst accumulator + singleEdgeString, snd accumulator + recursiveOnTargetNodes)

    /// Constructs the string for the edges and recursively calls the the illustration methods for the target nodes.
    and private addEdges (edges : HashSet<BlechEdge>) : string =
        // Accumulator is a triple consisting of (edgeStrings, recursiveNodeString, stateCount).
        // Accumulate the strings over the edges.
        let edgesAndRecursiveAccumulator = List.fold foldEdges ("","") (orderEdgeList (Seq.toList edges))

        // Put together the pieces and return ist.
        fst edgesAndRecursiveAccumulator + snd edgesAndRecursiveAccumulator

    /// Transforms a single cobegin branch to a string.
    and private cobeginBranchToString (branch :  VisGraph * Strength) : string =
        let final = match snd branch with
                        | Strong -> ""
                        | Weak -> "final" + blank
        
        final + "region" + blank + "{" + lnbreak + bodyToSctx (fst branch) + lnbreak + "}"

    /// Iterates recursevily over cobegin branches and transforms them to a .sctx string.
    and private cobeginBranchesToString (branchList : CobeginPayload) : string =
        match branchList with 
            | [head] -> cobeginBranchToString head
            | head :: tail -> cobeginBranchToString head + lnbreak + cobeginBranchesToString tail
            | [] -> ""

    /// Constructs a sctx string for an activity call.
    and private actCallToString (input : string list) (output : string list) (actName : string) : string =
        let concat = List.append input output

        let arguments = match concat.Length with 
                        | 0 -> ""
                        | 1 -> "(" + List.head concat + ")"
                        | _ -> "(" + List.fold commaConcatination (List.head concat) (List.tail concat) + ")"

        "is" + blank + actName + arguments        

    /// Adds nodes and edges recursively to a string, sctx conform. Returns a tuple where the first string is the sctx and the second string the state count.
    and private addNodesAndEdges (node : BlechNode) : string =
        // Add state, according to its settings (label, status) and mark node as visualized.
        let stateLabel : string = blank + "\"" + node.Payload.Label + "\""
        let initOrFinal : string = (match node.Payload.IsInitOrFinal.Init with | IsInit -> blank + "initial" | IsNotInit -> "") +
                                   (match node.Payload.IsInitOrFinal.Final with | IsFinal -> blank + "final" | IsNotFinal -> "")

        let stateString = blank + initOrFinal + " state s" + string node.Payload.StateCount + stateLabel 
        node.Payload.Visualize

        // Hierarchical states. Check if it is hierarchical, then match for regular body or activity.
        let complexState : string = match node.Payload.IsComplex with
                                        | IsComplex cmplx -> match cmplx.IsActivity with 
                                                                | IsActivity _ -> "{"  + lnbreak + activityToSctx node.Payload  + lnbreak + "}" + lnbreak
                                                                | IsNotActivity -> "{"  + lnbreak + bodyToSctx cmplx.Body  + lnbreak + "}" + lnbreak
                                        | IsSimple -> "" // Ok. Do nothing.
                                        | IsCobegin cbgn-> "{" + lnbreak + cobeginBranchesToString cbgn + lnbreak + "}" + lnbreak
                                        | IsActivityCall (input, output) -> actCallToString input output node.Payload.Label
        
        // If the node is a final node, we are finished, as there are no subsequent nodes.
        let edgeStringsAndRecursiveNodes =  match node.Payload.IsInitOrFinal.Final with
                                                | IsFinal -> ""
                                                | _ ->  // Add and illustrate edges. Calls method recursively to add the target states and their subsequent edges.
                                                        addEdges node.Outgoing

        stateString + blank + complexState + blank + edgeStringsAndRecursiveNodes

    /// Converts the body of an activity (or any other complex state) to a sctx-conform string.
    and private bodyToSctx (body : BlechVisGraph.VisGraph) : string =
        //BlechVisGraph.listNodes (Seq.toList body.Nodes)
        //BlechVisGraph.listEdges (Seq.toList body.Edges)
        // Find init node.
        //printfn "i get here"
        //List.map (fun (n:BlechNode) -> printfn "s%i - %s" n.Payload.StateCount n.Payload.IsInitOrFinal.ToString) (Seq.toList body.Nodes) |> ignore 
        let initNode = findInitNodeInHashSet body.Nodes
        //printfn "starter s%i" initNode.Payload.StateCount
        //List.map (fun (n:BlechNode) -> printfn "s%i" n.Payload.StateCount) (Seq.toList initNode.Successors) |> ignore 
        //printfn "i dont get here"
        
        // Add nodes and edges recursively. 
        addNodesAndEdges initNode

    /// Generates the sctx for an activity. Returns a string for this particular activity. Might be called recursively. Hence, it is its own method.
    and private activityToSctx (activityNode : NodePayload) : string = 
        //printfn "printing %s" activityNode.Label
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
        // Generates activities one by one and concats the single strings together
        // TODO We need to add variables in the beginning. Right now working with conditions as labels. In "if elses", we lose the information which comes first.
        match activities with 
            | head :: tail -> activityToSctx head.Payload + generate tail
            | [] -> ""