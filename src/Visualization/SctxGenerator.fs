module Blech.Visualization.SctxGenerator

    open System.Collections.Generic
    open Blech.Common.GenericGraph
    open Blech.Visualization.BlechVisGraph


    /// Constant variable for whitespaces.
    let private blank : string = " "


    /// Increase the state count. If the last letter of the string is a z, a new letter is added that starts at 'a'. TODO can we do better?
    let private increaseStateCount (currentCount : string ) : string = 
        // TODO simple implementation, just count up. Will break at z, because sctx only accepts chars and strings as identifiers.
        // How can I count up chars like char++?
        let charr = currentCount.[currentCount.Length - 1]

        let newChar = match charr with
                        | 'a' -> 'b'
                        | 'b' -> 'c'
                        | 'c' -> 'd'
                        | 'd' -> 'e'
                        | 'e' -> 'f'
                        | 'f' -> 'g'
                        | 'g' -> 'h'
                        | 'h' -> 'i'
                        | _   -> failwith "Not yet implemented. Can only visualize a certain amount of states for now."

        string newChar
       

    /// Method that converts a list of params to a string (sctx style).
    let private listParams (paramList : BlechVisGraph.paramList) (isInput : bool): string =
        let mutable output : string = ""

        for param : BlechVisGraph.param in paramList do 
            let mutable inOrOut : string = ""
            if isInput then
                inOrOut <- "input"
            else 
                inOrOut <- "output"

            output <- output + blank + inOrOut + " host \"" + param.TypeName + "\" " + param.Name
        output


    /// Adds nodes and edges recursively to a string, sctx conform. Returns a tuple where the first string is the sctx and the second string the state count.
    /// The state count is the current state identifier that is used in the sctx. It is passed recursively and increase there, the calls, however.
    /// Hence, the returned value is the one where the count starts from again. This way, the identifier is never used twice.
    let rec private addNodesAndEdges (node : Node<nodePayload, edgePayload>) (stateCount : string) : string * string =
        // Add state, according to its settings (label, status).
        let mutable output : string = ""
        let mutable stateLabel : string = ""
        let mutable initOrFinal : string = ""
        if(node.Payload.IsInit) then initOrFinal <- blank + "initial"
        if(node.Payload.IsFinal) then initOrFinal <- blank + "final" 
        if(not (System.String.Equals (node.Payload.Label, ""))) then stateLabel <- blank + "label" + blank + node.Payload.Label

        output <- output + blank + initOrFinal + " state " + stateCount + stateLabel

        // TODO hierarchical nodes would be started to be implemented HERE.
        // TODO, not yet implemented. Hierarchical constructs have not yet been extracted in Visualization.fs.
        match node.Payload.IsComplex with
            | IsComplex _ -> printf("Complex states are not yet supported in the sctx generation!!")
            | IsSimple -> () // Ok. Do nothing.
        
        // If the node is a final node, we are finished.
        if(node.Payload.IsFinal) then 
            (output, stateCount) 
        else 
            //Add edges to new states and recursively call this method.
            // Add and illustrate edges.
            let edges : HashSet<Edge<'NodeData, 'EdgeData>> = node.Outgoing
            let mutable edgeEnum = edges.GetEnumerator()
            let mutable currentCount = stateCount

            let mutable recursiveFollowupSctx = ""

            while edgeEnum.MoveNext() do
                let edge : Edge<nodePayload, edgePayload> = edgeEnum.Current
                let mutable edgeString = ""

                // Increase state count, since this identifier was used.
                currentCount <- increaseStateCount stateCount

                // TODO Condition needed as variable in sctx. For now, use labels. 
                if(edge.Payload.IsAwait) then  edgeString <- blank + "if true go to " + currentCount + " label \"" + edge.Payload.Label + "\""
                elif(edge.Payload.IsConditional) then  edgeString <- blank + "immediate if true go to " + currentCount + " label \"" + edge.Payload.Label + "\""
                elif(edge.Payload.IsImmediate) then edgeString <- blank + "immediate go to " + currentCount
                elif(edge.Payload.IsAbort) then edgeString <- blank + "if true abort to " + currentCount + " label \"" + edge.Payload.Label + "\""
                elif(edge.Payload.IsTerminal) then edgeString <- blank + "join to " + currentCount + " label \"" + edge.Payload.Label + "\""
                
                output <- output + edgeString

                // Call this method recursively for the target node. But add their sctx-code after the following edges. Reason being the sctx syntax.
                // The current count for the states is given as a parameter. The function returns it back and shows how far it was used. It is counted up from there.
                // TODO this might be an error due to the functional nature of the code. How is F# evaluated? Check this.
                let recursive = (addNodesAndEdges edge.Target currentCount)
                let sctxRecursive = fst(recursive)
                currentCount <- snd(recursive)
                recursiveFollowupSctx <- recursiveFollowupSctx + blank + sctxRecursive

            output <- output + blank + recursiveFollowupSctx

            (output, stateCount)
        

    /// Converts the body of an activity (or any other complex state) to a sctx-conform string.
    let private bodyToSctx (body : BlechVisGraph.VisGraph) : string =
        // Init.
        let mutable output : string = ""
        let mutable stateCount : string = "a";

        // Find init node.
        let mutable enumerator = body.Nodes.GetEnumerator()
        let phString : string = "emptyPlaceholder"
        let mutable initNode : Node<nodePayload, edgePayload> = Node.Create(new nodePayload(phString, IsSimple, false, false, PayloadAbsent))

        // Assign correct node to the variable.
        while enumerator.MoveNext() do
            let node : Node<nodePayload, edgePayload> = enumerator.Current
            if(node.Payload.IsInit) then initNode <- node else () // do nothing

        // Assert that it worked.
        if(System.String.Equals (initNode.Payload.Label, phString)) then failwith("Internal error. Given graph was errerous. II")

        // Add nodes and edges recursively.
        output <- output + fst(addNodesAndEdges initNode stateCount)

        output

    /// Generates the sctx for an activity. Returns a string for this particular activity.
    let private activityToSctx (activity : activityPayloadPresent) : string = 
        // Safety assert. Init with empty Payload.
        let actPayload = match(activity) with
                            | PayloadPresent a -> a // Ok. Do nothing.
                            | PayloadAbsent -> failwith("Can not continue. Expected the payload to be present.")
        
        // Init.
        let mutable output : string = ""
        
        // Activity name and parameters.
        output <- output + "scchart" + blank + actPayload.Name + blank + "{"

        output <- output + listParams actPayload.InputParams true
        output <- output + listParams actPayload.OutputParams false

        output <- output + bodyToSctx actPayload.ActivityBody

        output <- output + "}"
        output


    /// Generate sctx file content.
    let generate (graph : BlechVisGraph.VisGraph) : string = 
        // The sctx is put into a string. We do not need line breaks or indention luckily.
        let mutable sctx : string = ""

        // Graph should consists of node (representing the activity) containing the body. Find the node.
        let nodes : HashSet<Node<'NodeData, 'EdgeData>> = graph.Nodes
        let mutable enumerator = nodes.GetEnumerator()

        // Init variable with empty object.
        let phString : string = "emptyPlaceholder"
        let mutable activityNode : Node<nodePayload, edgePayload> = Node.Create(new nodePayload(phString, IsSimple, false, false, PayloadAbsent))

        // Assign correct node to the variable.
        while enumerator.MoveNext() do
            let node : Node<nodePayload, edgePayload> = enumerator.Current
            match node.Payload.ActivityPayloadPresent with
                | PayloadPresent _ -> activityNode <- node
                | PayloadAbsent -> () // do nothing, not the droid we are looking for

        // Assert that it worked.
        if(System.String.Equals (activityNode.Payload.Label, phString)) then failwith("Internal error. Given graph was errerous. I")

        // Node should contain the inner code and input output variables. Start with the outermost activity.
        // TODO We need to add variables in the beginning. Right now working with conditions as labels. In "if elses", we lose the information which comes first.
        sctx <- sctx + (activityToSctx activityNode.Payload.ActivityPayloadPresent) 

        sctx