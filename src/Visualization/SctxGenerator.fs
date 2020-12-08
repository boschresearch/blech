module Blech.Visualization.SctxGenerator

    open Blech.Common.GenericGraph
    open Blech.Visualization.BlechVisGraph
    open System.Collections.Generic

    /// Constant for whitespaces.
    let private blank : string = " "

    /// Constant for line breaks.
    let private lnbreak : string = "\n"

    /// Converts a single param to a string.
    let private listParam (param : param) (isInput : bool) : string =
        let inOrOut : string = 
            match isInput with
               | true -> "input"
               | false -> "output"

        // TODO anyone of these? Some sort of parsing. Pure signal problem might be due to name of the input/output.
        //output <- output + blank + inOrOut + blank + param.TypeName + blank + param.Name
        blank + inOrOut + " host \"" + param.typeName + "\" " + param.name + lnbreak            

    /// Method that converts a list of params to a string (sctx style).
    let rec private listParams (paramList : paramList) (isInput : bool) (accumulator : string) : string =
        match paramList with 
            | head :: tail -> listParam head isInput |> listParams tail isInput
            | [] -> accumulator

    /// Construct a string representing a single edge.
    let private singleEdge(edge : Edge<nodePayload, edgePayload>) (target : int): string =
        match edge.Payload.property with 
            | IsAwait ->  blank + "if true go to s" + string target + " label \"" + edge.Payload.label + "\"" + lnbreak
            | IsConditional ->  blank + "immediate if true go to s" + string target + " label \"" + edge.Payload.label + "\"" + lnbreak
            | IsImmediate -> blank + "immediate go to s" + string target + lnbreak
            | IsAbort -> blank + "if true abort to s" + string target + " label \"" + edge.Payload.label + "\"" + lnbreak
            | IsTerminal -> blank + "join to s" + string target + " label \"" + edge.Payload.label + "\"" + lnbreak

    /// Folding function that is used to fold a set of edges into their corresponding sctx strings.
    let rec foldEdges (accumulator : edgeAccumulator) (edge : Edge<nodePayload, edgePayload>) : edgeAccumulator =
        let singleEdgeString = singleEdge edge edge.Target.Payload.stateCount

        // Only visualize node if it has not been visualized yet.
        let recursiveOnTargetNodes = 
            match edge.Target.Payload.wasVisualized with
                | Visualized -> "" // ok do not visualize this node.
                | NotVisualized ->  addNodesAndEdges edge.Target

        (fst accumulator + singleEdgeString, snd accumulator + recursiveOnTargetNodes)

    /// Constructs the string for the edges and recursively calls the the illustration methods for the target nodes.
    and private addEdges (edges : HashSet<Edge<nodePayload, edgePayload>>) : string =
        // Accumulator is a triple consisting of (edgeStrings, recursiveNodeString, stateCount).
        // Accumulate the strings over the edges.
        let edgesAndRecursiveAccumulator = List.fold foldEdges ("","") (Seq.toList edges)

        // Put together the pieces and return ist.
        fst edgesAndRecursiveAccumulator + snd edgesAndRecursiveAccumulator


    /// Adds nodes and edges recursively to a string, sctx conform. Returns a tuple where the first string is the sctx and the second string the state count.
    and private addNodesAndEdges (node : Node<nodePayload, edgePayload>) : string =
        // Add state, according to its settings (label, status) and mark node as visualized.
        let stateLabel : string = blank + "\"" + node.Payload.label + "\""
        let initOrFinal : string = 
            match node.Payload.isInitOrFinal with
                | Init -> blank + "initial"
                | Final -> blank + "final"
                | Neither -> ""

        let stateString = blank + initOrFinal + " state s" + string node.Payload.stateCount + stateLabel + lnbreak 
        node.Payload.visualize

        // Hierarchical states. Check if it is hierarchical, then match for regular body or activity.
        let complexState : string = match node.Payload.isComplex with
                                        | IsComplex cmplx -> match cmplx.isActivity with 
                                                                | IsActivity _ -> "{"  + lnbreak + activityToSctx node.Payload  + lnbreak + "}" + lnbreak
                                                                | IsNotActivity -> "{"  + lnbreak + bodyToSctx cmplx.body  + lnbreak + "}" + lnbreak
                                        | IsSimple -> "" // Ok. Do nothing.
        
        // If the node is a final node, we are finished.
        match node.Payload.isInitOrFinal with
            | Final -> stateString
            | _ ->  // Add and illustrate edges. Calls method recursively to add the target states and their subsequent edges.
                    let edgeStringsAndRecursiveNodes = addEdges node.Outgoing
                    let output = stateString + blank + complexState + blank + edgeStringsAndRecursiveNodes

                    output
        

    /// Converts the body of an activity (or any other complex state) to a sctx-conform string.
    and private bodyToSctx (body : BlechVisGraph.VisGraph) : string =
        // Find init node.
        let initNode = 
            body.Nodes 
            |> Seq.toList 
            |> List.tryFind (fun node -> match node.Payload.isInitOrFinal with Init -> true | _ -> false) 
            |> (fun option -> match option.IsSome with true -> option.Value | false -> failwith("Internal error. Given graph was errerous. II"))
        
        // Add nodes and edges recursively.
        addNodesAndEdges initNode

    /// Generates the sctx for an activity. Returns a string for this particular activity. Might be called recursively. Hence, it is its own method.
    and private activityToSctx (activityNode : nodePayload) : string = 
        // Safety assert. Init with empty Payload.
        let complexNode = match(activityNode.isComplex) with
                            | IsComplex a -> a
                            | IsSimple -> failwith("Can not continue. Expected a complex state.")
        
        let activityProps = match(complexNode.isActivity) with
                            | IsActivity a -> a
                            | IsNotActivity -> failwith("Can not continue. Expected an activity.")

        
        // Construct the resulting string..
        "scchart" + blank + activityNode.label + blank
                  + "{" + lnbreak
                  + listParams activityProps.inputParams true "" 
                  + listParams activityProps.outputParams false ""
                  + bodyToSctx complexNode.body
                  + "}"


    /// Generate sctx file content.
    let generate (activity : Node<nodePayload, edgePayload>) : string = 
        // Node should contain the inner code and input output variables. Start with the outermost activity. Activity in own method due do potential recursive calls.
        // TODO We need to add variables in the beginning. Right now working with conditions as labels. In "if elses", we lose the information which comes first.
        activityToSctx activity.Payload