module Blech.Visualization.SctxGenerator

    open Blech.Common.GenericGraph
    open Blech.Visualization.BlechVisGraph
    open System.Collections.Generic

    /// Constant variable for whitespaces.
    let private blank : string = " "

    /// Gives the xth element of a triple.
    let private frst (a,_,_) = a
    let private scnd (_,b,_) = b
    let private thrd (_,_,c) = c  

    /// Converts a single param to a string.
    let private listParam (param : param) (isInput : bool) : string =
        let inOrOut : string = 
            match isInput with
               | true -> "input"
               | false -> "output"

        // TODO anyone of these? Some sort of parsing. Pure signal problem might be due to name of the input/output.
        //output <- output + blank + inOrOut + blank + param.TypeName + blank + param.Name
        blank + inOrOut + " host \"" + param.typeName + "\" " + param.name             

    /// Method that converts a list of params to a string (sctx style).
    let rec private listParams (paramList : paramList) (isInput : bool) (accumulator : string) : string =
        match paramList with 
            | head :: tail -> listParam head isInput |> listParams tail isInput
            | [] -> accumulator

    /// Construct a string representing a single edge.
    let private singleEdge(edge : Edge<nodePayload, edgePayload>) (count : int): string =
        match edge.Payload.property with 
            | IsAwait ->  blank + "if true go to s" + string count + " label \"" + edge.Payload.label + "\""
            | IsConditional ->  blank + "immediate if true go to s" + string count + " label \"" + edge.Payload.label + "\""
            | IsImmediate -> blank + "immediate go to s" + string count
            | IsAbort -> blank + "if true abort to s" + string count + " label \"" + edge.Payload.label + "\""
            | IsTerminal -> blank + "join to s" + string count + " label \"" + edge.Payload.label + "\""

    /// Folding function that is used to fold a set of edges into their corresponding sctx strings.
    let rec foldEdges (accumulator : edgeAccumulator) (edge : Edge<nodePayload, edgePayload>) : edgeAccumulator =
        // String for edge.
        let currentCount = thrd accumulator + 1
        let singleEdgeString = singleEdge edge currentCount
        // Recursive calls on target nodes.
        let recursiveOnTargetNodes = addNodesAndEdges edge.Target currentCount
        let recursiveSctx = fst (recursiveOnTargetNodes)
        let countAfterRecursion = snd (recursiveOnTargetNodes)

        (frst accumulator + singleEdgeString, scnd accumulator + recursiveSctx, countAfterRecursion)

    /// Constructs the string for the edges and recursively calls the the illustration methods for the target nodes.
    and private addEdges (edges : HashSet<Edge<nodePayload, edgePayload>>) (stateCount : int) : string =
        // Accumulator is a triple consisting of (edgeStrings, recursiveNodeString, stateCount).
        // Accumulate the strings over the edges.
        let edgesAndRecursiveAccumulator = List.fold foldEdges ("","", stateCount) (Seq.toList edges)

        // Put together the pieces and return ist.
        frst edgesAndRecursiveAccumulator + scnd edgesAndRecursiveAccumulator


    /// Adds nodes and edges recursively to a string, sctx conform. Returns a tuple where the first string is the sctx and the second string the state count.
    /// The state count is the current state identifier that is used in the sctx. It is passed recursively and increase there, the calls, however.
    /// Hence, the returned value is the one where the count starts from again. This way, the identifier is never used twice.
    and private addNodesAndEdges (node : Node<nodePayload, edgePayload>) (stateCount : int) : string * int =
        // Add state, according to its settings (label, status).
        let stateLabel : string = blank + "label" + blank + node.Payload.label
        let initOrFinal : string = 
            match node.Payload.isInitOrFinal with
                | Init -> blank + "initial"
                | Final -> blank + "final"
                | Neither -> ""

        let stateString = blank + initOrFinal + " state s" + string stateCount + stateLabel

        // TODO hierarchical nodes would be started to be implemented HERE.
        // TODO, not yet implemented. Hierarchical constructs have not yet been extracted in Visualization.fs.
        match node.Payload.isComplex with
            | IsComplex _ -> printf("Complex states are not yet supported in the sctx generation!!")
            | IsSimple -> () // Ok. Do nothing.
        
        // If the node is a final node, we are finished.
        match node.Payload.isInitOrFinal with
            | Final -> (stateString, stateCount) 
            | _ ->  // Add and illustrate edges. Calls method recursively to add the target states and their subsequent edges.
                    let edgeStringsAndRecursiveNodes = addEdges node.Outgoing stateCount 
                    let output = stateString + blank + edgeStringsAndRecursiveNodes

                    (output, stateCount)
        

    /// Converts the body of an activity (or any other complex state) to a sctx-conform string.
    let private bodyToSctx (body : BlechVisGraph.VisGraph) : string =
        // Find init node.
        let initNode = body.Nodes |> Seq.toList |> List.tryFind (fun node -> match node.Payload.isInitOrFinal with Init -> true | _ -> false) |> (fun option -> match option.IsSome with true -> option.Value | false -> failwith("Internal error. Given graph was errerous. II"))
        
        // Add nodes and edges recursively.
        fst(addNodesAndEdges initNode 0)

    /// Generates the sctx for an activity. Returns a string for this particular activity. Might be called recursively. Hence, it is its own method.
    let private activityToSctx (activityNode : nodePayload) : string = 
        // Safety assert. Init with empty Payload.
        let complexNode = match(activityNode.isComplex) with
                            | IsComplex a -> a
                            | IsSimple -> failwith("Can not continue. Expected a complex state.")
        
        let activityProps = match(complexNode.isActivity) with
                            | IsActivity a -> a
                            | IsNotActivity -> failwith("Can not continue. Expected an activity.")

        
        // Construct the resulting string..
        "scchart" + blank + activityNode.label + blank 
                  + "{" 
                  + listParams activityProps.inputParams true "" 
                  + listParams activityProps.outputParams false ""
                  + bodyToSctx complexNode.body
                  + "}"


    /// Generate sctx file content.
    let generate (activity : Node<nodePayload, edgePayload>) : string = 
        // Node should contain the inner code and input output variables. Start with the outermost activity. Activity in own method due do potential recursive calls.
        // TODO We need to add variables in the beginning. Right now working with conditions as labels. In "if elses", we lose the information which comes first.
        (activityToSctx activity.Payload) 