module Blech.Visualization.BlechVisGraph

    open Blech.Common
    open Blech.Frontend.BlechTypes

    /// Specifies a (input or output parameter). First String specifies the type of the Parameter, second String specifies the name.
    type param = { typeName: string; name: string}

    /// Functions for transforming Blech paremters to my own parameter type.    
    let paramToParam = fun (paramDec : ParamDecl) -> {typeName = paramDec.datatype.ToString(); name = paramDec.name.basicId}
    let extParamToParam = fun (extVarDecl : ExternalVarDecl) -> {typeName = extVarDecl.datatype.ToString(); name = extVarDecl.name.basicId}

    /// List of params. Might need some operations?                
    type paramList = param list
   
    /// Facadeing the complex expression, for short: Visgraph.
    type VisGraph = GenericGraph.Graph<nodePayload, edgePayload>      

    /// Payload to enter in an activity graph.
    and activityPayload = {inputParams : paramList; outputParams : paramList}

    /// Shows if activity payload is present
    and isActivity = IsActivity of activityPayload | IsNotActivity
    
    /// Content of a complex node.
    and complexNode = {body : VisGraph; isActivity : isActivity}
    
    /// Type to match whether a node is simple or complex.
    and complexOrSimple = IsComplex of complexNode | IsSimple

    /// Determines whether something is "Initial" or "Final".
    and InitOrFinalOrNeither = Init | Final | Neither

    /// Payload for a node.
    and nodePayload = { label : string; isComplex : complexOrSimple ; isInitOrFinal : InitOrFinalOrNeither}

    /// Determines what kind of edge the edge ist.
    and edgeProperty = IsAwait | IsConditional | IsImmediate| IsTerminal |IsAbort

    /// Payload for an edge.
    and edgePayload = { label : string; property : edgeProperty}

    /// Type for an edge accumulator.
    and edgeAccumulator = string * string * int