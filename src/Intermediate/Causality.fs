// Copyright (c) 2019 - for information on the respective copyright owner
// see the NOTICE file and/or the repository 
// https://github.com/boschresearch/blech.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

module Blech.Intermediate.Causality

open System.Collections.Generic

open Blech.Common
open Blech.Common.Range

open ProgramGraph

module GenericGraph = Blech.Common.GenericGraph

//=============================================================================
// Functions that create Diagnostic messages (errors)
//=============================================================================

let private getRangeOrDieTrying (node: Node) = 
    match node.Payload.Line with
    | Some r -> r
    | None -> failwith "Graph node does not have source position information. Compiler bug!"

/// Given a set of nodes, get all ranges that are not range0
/// return them in ascending order
let private getSomeRanges (nodes: Node seq) =
    let rangeComparer (r1: range) (r2: range) =
        if r1.FileName = r2.FileName then
            if r1.StartLine = r2.StartLine then
                Operators.compare r1.StartColumn r2.StartColumn
            else
                Operators.compare r1.StartLine r2.StartLine
        else
            r1.FileName.CompareTo r2.FileName
    nodes 
    |> Seq.choose (fun n -> n.Payload.Line)
    |> Seq.filter ((<>) range0) // not equal range0
    |> Seq.toArray
    |> Array.sortWith rangeComparer

let private mkDiagnosticAliasWWerror memLoc (nameRange1, _) (nameRange2, n2) : Diagnostics.Diagnostic =
    let secondRange = getRangeOrDieTrying n2
    let identifier = memLoc.ToString()
    let mainInfo: Diagnostics.Information =
        { range = secondRange
          message = sprintf "Write-write conflict. %s or an alias thereof occurs multiple times in the output list of the sub program call." identifier }
    let context: Diagnostics.ContextInformation list =
        [ { range = nameRange1
            message = "First occurence of output argument."
            isPrimary = false }
          { range = nameRange2
            message = "Subsequent alias of the same output argument."
            isPrimary = true } ]
    let note = [ "If this usage is intended, consider using the \"shares\" keyword when declaring the formal parameters of the subprogram." ]
    { phase = Diagnostics.Phase.Causality
      level = Diagnostics.Level.Error
      main = mainInfo
      context = context
      note = note }

let private mkDiagnosticWWerror (memLoc: AccessLabel) (nameRange1, _) (nameRange2, n2) : Diagnostics.Diagnostic =
    let secondRange = getRangeOrDieTrying n2
    let messagesForDataAccess =
        let identifier = memLoc.ToString()
        let mainInfo: Diagnostics.Information =
            { range = secondRange
              message = sprintf "Write-write conflict. %s is written concurrently." identifier }
        let context: Diagnostics.ContextInformation list =
            [ { range = nameRange1
                message = "First write access."
                isPrimary = false }
              { range = nameRange2
                message = "Conflicting concurrent write access."
                isPrimary = true } ]
        let note = [ "There may be only one writer per variable in the scope of a \"cobegin\" statement." ]
        mainInfo, context, note
    let messagesForProgramAccess (subProgName: Blech.Frontend.CommonTypes.QName) =
        let identifier = subProgName.basicId
        let mainInfo: Diagnostics.Information =
            { range = secondRange
              message = sprintf "Singleton subprogram %s cannot be called concurrently." identifier }
        let context: Diagnostics.ContextInformation list =
            [ { range = nameRange1
                message = "First call."
                isPrimary = false }
              { range = nameRange2
                message = "Conflicting concurrent call."
                isPrimary = true } ]
        let note = [ "A function or activity is either explicitly declared or inferred as a singleton because it calls singletons. There may be no concurrent calls to the same singleton subprogram." ]
        mainInfo, context, note
    let mainInfo, context, note =
        match memLoc with
        | SubProg subProgName ->
            messagesForProgramAccess subProgName
        | Cur _ | Prev _ | Next _ ->
            messagesForDataAccess
    { phase = Diagnostics.Phase.Causality
      level = Diagnostics.Level.Error
      main = mainInfo
      context = context
      note = note }

let private mkDiagnosticAliasWRerror memLoc (nameRangeW, _) (nameRangeR, nr) : Diagnostics.Diagnostic =
    let secondRange = getRangeOrDieTrying nr
    let identifier = memLoc.ToString()
    let mainInfo: Diagnostics.Information =
        { range = secondRange
          message = sprintf "Read-write conflict. %s or an alias thereof occurs both in the input and output list of the sub program call." identifier }
    let context: Diagnostics.ContextInformation list =
        [ { range = nameRangeW
            message = "Output argument."
            isPrimary = false }
          { range = nameRangeR
            message = "Input argument."
            isPrimary = true } ]
    let note = [ "If this usage is intended, consider using the \"shares\" keyword when declaring the formal parameters of the subprogram." ]
    { phase = Diagnostics.Phase.Causality
      level = Diagnostics.Level.Error
      main = mainInfo
      context = context
      note = note }

let private mkDiagnosticInstantError (subGraph: Graph) : Diagnostics.Diagnostic =
    let ranges = subGraph.Nodes |> getSomeRanges
    assert (ranges.Length > 0) // At least some node in the graph should carry a range information
    let allRanges = 
        ranges 
        |> Seq.reduce Range.unionRanges // a control flow path never spans multiple files, so that's fine
    let mainInfo: Diagnostics.Information =
        { range = allRanges
          message = "There is an instantaneous control path." }
    let context: Diagnostics.ContextInformation list =
        ranges
        |> Seq.map (fun r -> 
            { Diagnostics.ContextInformation.range = r
              Diagnostics.ContextInformation.message = "A node in the instantaneous cycle."
              Diagnostics.ContextInformation.isPrimary = false }
            )
        |> List.ofSeq
    let note = [ "Every unbounded cycle must be cut by an \"await\" or \"run\" statement."
                 "A frequent cause for this error is that the body of a while-loop may be skipped."
                 "In this case, use repeat..end instead of while loops to ensure the body is not skipped." ]
    { phase = Diagnostics.Phase.Causality
      level = Diagnostics.Level.Error
      main = mainInfo
      context = context
      note = note }

let rec private ctxInfoFromCircle (ctx: ResizeArray<Diagnostics.ContextInformation>) (visited: HashSet<Node>) (edge: Edge) =
    let target = edge.Target
    let addContextInfo m wr rr isPrimaryInfo =
        { Diagnostics.ContextInformation.range = wr
          Diagnostics.ContextInformation.message = sprintf "Writes %s." (m.ToString())
          Diagnostics.ContextInformation.isPrimary = isPrimaryInfo }
        |> ctx.Add
        { Diagnostics.ContextInformation.range = rr
          Diagnostics.ContextInformation.message = sprintf "Reads %s." (m.ToString())
          Diagnostics.ContextInformation.isPrimary = isPrimaryInfo }
        |> ctx.Add
    
    if visited.Contains target then
        // return errors
        match edge.Payload with
        | DataFlow (m, wr, rr) -> addContextInfo m wr rr true
        | _ -> () // for WR error do not spell out ctrl flow edges
    else
        // continue exploring cycle
        visited.Add target |> ignore
        match edge.Payload with
        | DataFlow (m, wr, rr) -> addContextInfo m wr rr false
        | _ -> ()
        target.Outgoing // there should be only one actually
        |> Seq.iter (ctxInfoFromCircle ctx visited)

let private mkDiagnosticWRerror (cycle: Graph) : Diagnostics.Diagnostic =
    let ranges = cycle.Nodes |> getSomeRanges
    let allRanges = 
        ranges 
        |> Seq.reduce Range.unionRanges // a causality error never spans multiple files, so that's fine
    let mainInfo: Diagnostics.Information =
        { range = allRanges
          message = "There is a cyclic write-read path." }

    let startEdge = Seq.head cycle.Edges
    let contextInfos = ResizeArray()
    let visited = HashSet()
    visited.Add startEdge.Source |> ignore
    ctxInfoFromCircle contextInfos visited startEdge

    let note = [ "To break a causality cycle, use \"prev\" on some read variable." ]
    { phase = Diagnostics.Phase.Causality
      level = Diagnostics.Level.Error
      main = mainInfo
      context = Seq.toList contextInfos
      note = note }


//=============================================================================
// Checking for causality errors
//=============================================================================

/// Check for write-write conflicts
/// for every written variable, run through the list of nodes writing it and check for each pair if they are concurrent
let rec private checkWW memLoc nodeList logger =
    let logIfConcurrent x y =
        if snd x = snd y then
            Diagnostics.Logger.addDiagnostic logger (mkDiagnosticAliasWWerror memLoc x y) 
        elif areConcurrent (snd x) (snd y) then
            Diagnostics.Logger.addDiagnostic logger (mkDiagnosticWWerror memLoc x y) 
        else ()
    match nodeList with
    | node :: rest ->
        rest
        |> List.iter (logIfConcurrent node)
        checkWW memLoc rest logger
    | _ -> ()


// cycle detection
// for this perform SCC search on the graph where await locations are removed
// now you find potentially infinite reactions due to control flow cycles and 
// you find causality cycles
let private determineCycles pg =
    //let cycleAnalysisGraph = GenericGraph.clone pg.Graph // deep copy graph for further modification
    let mapping, cycleAnalysisGraph = GenericGraph.Graph<_,_>.SubGraphFromNodes pg.Graph.Nodes
    // Transition where time spent are the "tick" transitions 
    let filterDelaying (edge: Edge) =
        match edge.Payload with
        | Tick _ -> true 
        | _ -> false

    cycleAnalysisGraph.Edges
    |> Seq.filter filterDelaying
    |> Seq.toList   // important step to prevent error "Collection was modified; enumeration operation may not execute"
    |> List.iter cycleAnalysisGraph.RemoveEdge // remove all tick edges since no causality cycle can pass through an await

    let pairs = GenericGraph.johnson75 cycleAnalysisGraph // decompose the resulting graph into cycles
    [for pair in pairs do yield (GenericGraph.mergeMappings mapping (fst pair), snd pair)]

open Blech.Frontend.BlechTypes
// C&P from ProgramGraph.fs with modifications
let rec internal findNameWritten wrPair (tlhs: TypedLhs) =
    let newWrPair (tml: TypedMemLoc) =
        tml.FindAllIndexExpr 
        |> List.fold findNameRead wrPair
    match tlhs.lhs with
    | Wildcard -> wrPair
    | ReturnVar -> wrPair
    | LhsCur tml ->
        let wrp1 = newWrPair tml 
        ((Cur tml) :: fst wrp1, snd wrp1)
    | LhsNext tml ->
        let wrp1 = newWrPair tml 
        ((Next tml) :: fst wrp1, snd wrp1)

and internal findNameRead wrPair trhs =
    let processFields fields =
        fields
        |> List.unzip
        |> snd // here we get a list of all rhs expr used in this literal
        |> List.fold findNameRead wrPair

    match trhs.rhs with
    | RhsCur tml -> 
        // check for array index expressions and recursively call addNameRead on them
        let newWrPair =
            tml.FindAllIndexExpr 
            |> List.fold findNameRead wrPair
        (fst newWrPair, (Cur tml) :: snd newWrPair)
    | Prev _ -> wrPair // this is irrelevant for causality
    | FunCall (name, ins, outs) ->
        // add local names for this call
        let wrp1 = ins |> List.fold findNameRead wrPair
        outs |> List.fold findNameWritten wrp1 
    | BoolConst _ 
    | IntConst _
    | BitsConst _
    | NatConst _
    | FloatConst _ 
    | ResetConst _ -> wrPair
    | StructConst structFieldExprList ->
        structFieldExprList |> processFields
    | ArrayConst elems ->
        elems |> processFields
    | Convert (expr, _, _)
    | Bnot expr
    | Neg expr -> findNameRead wrPair expr
    | Conj (ex1, ex2)
    | Disj (ex1, ex2)
    | Band (ex1, ex2)
    | Bor (ex1, ex2)
    | Bxor (ex1, ex2)
    | Shl (ex1, ex2)
    | Shr (ex1, ex2)
    | Sshr (ex1, ex2)
    | Rotl (ex1, ex2)
    | Rotr (ex1, ex2)
    | Les (ex1, ex2)
    | Leq (ex1, ex2)
    | Equ (ex1, ex2)
    | Add (ex1, ex2)
    | Sub (ex1, ex2)
    | Mul (ex1, ex2)
    | Div (ex1, ex2)
    | Mod (ex1, ex2) ->
        findNameRead wrPair ex1
        |> findNameRead <| ex2

let private transitiveBackwardClosureWR (pg: ProgramGraph) =
    let rec fix f x =
        let res = Seq.append x (f x) |> Seq.distinct
        if Seq.length res = Seq.length x then res
        else fix f res
    // find all nodes that are the source of a WR edge
    let relevantNodes = 
        pg.Graph.Nodes |> Seq.filter (fun n -> n.Outgoing |> Seq.exists isDataFlow)
    // for every source walk backwards to immediate control flow predecessors
    for n in relevantNodes do
        // collect all their corresponding WR links
        let allWRedges = n.Outgoing |> Seq.filter isDataFlow
        let immediatePredecessors (x: Node) =
            x.Incoming
            |> Seq.filter isImmediateTransition
            |> Seq.map (fun e -> e.Source)
        let instantaneousPredecessors = seq{n} |> fix (Seq.map immediatePredecessors >> Seq.collect id) 
        // add all WR edges of original node to resp. predecessor
        instantaneousPredecessors
        |> Seq.iter (fun p ->
            allWRedges
            |> Seq.iter (fun e -> 
                if areConcurrent p e.Target then
                    pg.Graph.AddEdge e.Payload p e.Target
                else
                    ()
                )
            )
    ()

let private addWRedges context name writtenVar logger =
    try
        let nodesReading = context.subprogReadNodes.[name].[writtenVar]
        let nodesWriting = context.subprogWrittenNodes.[name].[writtenVar]
        let pg = context.pgs.[name]
        nodesWriting 
        |> Seq.iter (fun (rangeInWN, writingNode) -> // for every writing node
            nodesReading 
            |> Seq.iter(fun (rangeInRN, readingNode) -> // check every reading node
                if writingNode = readingNode then
                    match writingNode.Payload.Typ with
                    // it is OK if the node is an assignment where the
                    // lhs only writes "name", and
                    // rhs only reads "name"
                    | ActionLocation (Action.Assign (_, l, r)) ->
                        let wrp1 = findNameRead ([],[]) r
                        let wrp2 = findNameWritten ([],[]) l
                        if List.contains writtenVar (fst wrp1) && List.contains writtenVar (snd wrp1)
                           || List.contains writtenVar (fst wrp2) && List.contains writtenVar (snd wrp2) then
                            Diagnostics.Logger.addDiagnostic
                                logger 
                                (mkDiagnosticAliasWRerror 
                                    writtenVar 
                                    (rangeInWN, writingNode) 
                                    (rangeInRN, readingNode)
                                )
                        else ()
                    // otherwise this is an aliasing error
                    | _ ->
                        Diagnostics.Logger.addDiagnostic
                            logger 
                            (mkDiagnosticAliasWRerror 
                                writtenVar 
                                (rangeInWN, writingNode) 
                                (rangeInRN, readingNode)
                            ) 
                elif areBothInSurfOrDepth pg.Graph writingNode readingNode then
                    pg.Graph.AddEdge (DataFlow (writtenVar, rangeInWN, rangeInRN)) writingNode readingNode // and in that case add a WR edge
                else
                    ()
                )
            )
        transitiveBackwardClosureWR pg
    with
        | :? System.Collections.Generic.KeyNotFoundException -> () //Seq.empty // if the name is not found, there is no dependency to add


let private checkWR (mapAndCycle: Dictionary<_,_> * Graph) logger =
    // find least common fork (may not exist if root is the lca)
    if (snd mapAndCycle).Nodes.Count > 1 then // every SCC with more than one element contains a cycle
                                              // this condition also prevents us from finding AliasWRerror a second time here
        (snd mapAndCycle).FilterEdges (function DataFlow _ -> true | _ -> false)
        |> Seq.isEmpty
        |> function 
            | true ->
                // if there were no DataFlow edges in the cycle, then it was an instantaneous control flow cycle
                Diagnostics.Logger.addDiagnostic logger (mkDiagnosticInstantError <| snd mapAndCycle) 
            | false -> 
                // check that cycle does not pass through lcf of nodes involved in the data flow
                let forksForDataFlowPairs = 
                    (snd mapAndCycle).FilterEdges (function DataFlow _ -> true | _ -> false)
                    |> Seq.map (fun edge -> leastCommonFork edge.Source edge.Target )
                    |> Seq.choose id // remove Nones, flatten Some to value
                    |> Seq.distinct // distinct lcf between directly data-flow related nodes
                    |> Seq.toList

                let rec mapReduce lcfs =
                    match lcfs with
                    | [] -> // no fork found ==> cycle on top level or immediate control flow (neither is possible!!)
                        failwith "why did I end up here?"
                    | [x] -> x // one fork to rule them all
                    | x1 :: x2 :: tail -> 
                        [leastCommonFork x1 x2]
                        |> List.choose id // remove Nones, flatten Some to value
                        |> (@) <| tail
                        |> List.distinct // distinct lcf between directly data-flow related nodes
                        |> mapReduce
                
                let theFork = mapReduce forksForDataFlowPairs
                if (fst mapAndCycle).ContainsKey theFork then () // there is no error actually
                else Diagnostics.Logger.addDiagnostic logger (mkDiagnosticWRerror <| snd mapAndCycle) 

let private checkCausality context causalityLogger activityName =
    // check write-write errors
    context.subprogWrittenNodes.[activityName]
    |> Seq.iter (fun memLoc -> checkWW memLoc.Key (Seq.toList memLoc.Value) causalityLogger)

    // introduce WR edges for causality cycle check
    context.subprogWrittenNodes.[activityName]
    |> Seq.iter (fun varName -> addWRedges context activityName varName.Key causalityLogger)
        
    // check write-read and instantaneous cycles
    determineCycles context.pgs.[activityName]
    |> Seq.iter (fun mapAndCycle -> checkWR mapAndCycle causalityLogger)

let private getLoggerAfterCausalityCheck context = 
    let causalityLogger = Diagnostics.Logger.create()
    context.pgs.Keys
    |> Seq.iter (fun name -> checkCausality context causalityLogger name)

    causalityLogger
        
/// Inserts DataFlow edges into the graphs as a side effect.
/// These are relevant both for checking causality and for 
/// Block generation and ordering.
let private checkCausalityOfContext context =
    let causalityLogger = getLoggerAfterCausalityCheck context

    // for every activity write its program graph
    // to the logger (now including the data flow edges)
    context.pgs
    |> Seq.iter(fun kvp -> 
        Blech.Common.Logging.log6 "Main" ("program graph for " + kvp.Key.ToString() + "\n" + kvp.Value.ToString())
        )
    
    if Diagnostics.Logger.hasErrors causalityLogger then
        Error causalityLogger
    else
        Ok context.pgs

let checkPackCausality (lut, pack) =
    createPGofPackage (lut, pack) |> checkCausalityOfContext