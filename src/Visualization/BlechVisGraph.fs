module Blech.Visualization.BlechVisGraph

    open Blech.Common
    open Blech.Frontend.BlechTypes

    /// Specifies a (input or output parameter). First String specifies the type of the Parameter, second String specifies the name.
    type param =
        struct
            val TypeName : string
            val Name : string
            new(typeName, name) = {TypeName = typeName; Name = name}
        end

    /// List of params. Might need some operations?                
    type paramList = param list

    /// Recursively construct the parameterList. TODO check if the chosen type name and name generation are valid.
    let rec constructParamList (input : ParamDecl list) (outputList: paramList) : paramList =
            match input with
                | head :: tail -> constructParamList tail (new param("Type Name: " + head.datatype.ToString(), "Name: " + head.name.ToString())::outputList)
                | [] -> []

    /// Recursively construct the parameterList. TODO check if the chosen type name and name generation are valid.
    let rec constructParamList2 (input : ExternalVarDecl list) (outputList: paramList) : paramList =
            match input with
                | head :: tail -> constructParamList2 tail (new param("Type Name: " + head.datatype.ToString(), "Name: " + head.name.ToString())::outputList)
                | [] -> []

   
    /// Facadeing the complex expression, for short: Visgraph.
    type VisGraph = GenericGraph.Graph<nodePayload, edgePayload>      

    /// Payload to enter in an activity graph.
    and activityPayload =
        struct
            val Name : string
            val InputParams : paramList
            val OutputParams : paramList
            val ActivityBody : VisGraph
            new(name, inputParams, outputParams, activityBody) = {Name = name; InputParams = inputParams; OutputParams = outputParams; ActivityBody = activityBody}
        end
        
    /// Shows if activity payload is present
    and activityPayloadPresent = 
        | PayloadPresent of activityPayload
        | PayloadAbsent

    and complexNode =
            struct
            val Label : string
            val Body : VisGraph
            new(label, body) = {Label = label; Body = body}
        end

    and complexOrSimpleNode =
        | IsComplex of complexNode
        | IsSimple

    /// Payload for a node.
    /// If node represents an activity, use activityPayloadPresent instead of the IsComplex!
    and nodePayload =
        struct
            val Label : string
            val IsComplex : complexOrSimpleNode
            val IsInit : bool
            val IsFinal : bool
            val ActivityPayloadPresent : activityPayloadPresent
            new(label, isComplex, isInit, isFinal, activityPayloadPresent) = {Label = label; IsComplex = isComplex; IsInit = isInit; IsFinal = isFinal; ActivityPayloadPresent = activityPayloadPresent}
        end

    /// Payload for an edge.
    /// Mind the correct use of the properties ! IsAwait is for await statements, isConditional is for if-else, repeat and while. IsImmediate for regular transition flow.
    /// IsTerminal for terminating complex states. IsAbort for aborting states.
    and edgePayload =
        struct
            val Label : string
            val IsAwait : bool
            val IsConditional : bool
            val IsImmediate : bool
            val IsTerminal : bool
            val IsAbort : bool
            new(label, isAwait, isConditional, isImmediate, isTerminal, isAbort) = {Label = label; IsAwait = isAwait; IsConditional = isConditional; IsImmediate = isImmediate; IsTerminal = isTerminal; IsAbort = isAbort}
        end