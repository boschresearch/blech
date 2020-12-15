module Blech.Visualization.BlechVisGraph

    open Blech.Common
    open Blech.Frontend.BlechTypes
    open Blech.Common.GenericGraph
    open Blech.Frontend.CommonTypes

    /// Specifies a (input or output parameter). First String specifies the type of the Parameter, second String specifies the name.
    type param = { typeName: string; name: string}

    /// Gives the xth element of a triple.
    let frst (a,_,_) = a
    let scnd (_,b,_) = b
    let thrd (_,_,c) = c  

    /// List of params. Might need some operations?                
    type paramList = param list
   
    /// Facadeing the complex expression, for short: Visgraph.
    type VisGraph = GenericGraph.Graph<nodePayload, edgePayload>      

    /// Payload to enter in an activity graph.
    and activityPayload = {inputParams : paramList; outputParams : paramList}

    /// Payload to fill into a cobegin node.
    and cobeginPayload = (VisGraph * Strength) list

    /// Shows if activity payload is present
    and isActivity = IsActivity of activityPayload | IsNotActivity
    
    /// Content of a complex node.
    and complexNode = {body : VisGraph; isActivity : isActivity}
    
    /// Type to match whether a node is simple or complex or a cobegin node. Cobegin nodes are very different from others due to their concurrenc nature.
    /// IsActivityCall consists of the input and outpur variablenames
    and complexOrSimpleOrCobegin = IsComplex of complexNode | IsSimple | IsCobegin of cobeginPayload | IsActivityCall of (string list * string list)

    /// Determines whether something is "Initial" or "Final".
    and InitOrFinalOrNeither = Init | Final | Neither

    /// Determines if a node closes an if-else case.
    and StateCount = int

    /// Indicating, if a node has been transformed to sctx (visualized) or not.
    and wasVisualized = Visualized | NotVisualized

    /// Payload for a node.
    and nodePayload = {label : string; isComplex : complexOrSimpleOrCobegin ; isInitOrFinal : InitOrFinalOrNeither; stateCount : StateCount; mutable wasVisualized : wasVisualized}
        with member x.visualize = x.wasVisualized <- Visualized

    /// Determines what kind of edge the edge ist.
    and edgeProperty = IsAwait | IsConditional | IsImmediate | IsTerminal | IsAbort

    /// Payload for an edge.
    and edgePayload = { label : string; property : edgeProperty}

    /// Type for an edge accumulator. Edge String * Recursive Node Strings.
    and edgeAccumulator = string * string

    /// Type for sequentially constructing the graph. Consists of: current graph, previous available node for connection and current state count (for distinct state identifiers.)
    and GraphBuilder = VisGraph * Node<nodePayload, edgePayload> * int