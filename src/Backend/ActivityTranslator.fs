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

/// This module contains all functionality which is specific for the
/// translation of Blech activities to C code.

[<RequireQualifiedAccess>]
module Blech.Backend.ActivityTranslator

open System.Collections.Generic

open Blech.Common
open Blech.Common.Range
open Blech.Common.PPrint

open Blech.Frontend
open Blech.Frontend.CommonTypes
open Blech.Frontend.PrettyPrint.DocPrint
open Blech.Frontend.BlechTypes

open Blech.Intermediate
open Blech.Intermediate.BlockGraph

open Blech.Backend

open Normalisation
open CPdataAccess2
open CPrinter


let rec private cpAction ctx curComp action =
    match action with
    | Action.Nothing -> txt ""
    | Action.VarDecl v ->
        // If this declares a constant, do not generate any code here. The
        // declaration will appear on the top level.
        if v.IsConst then
            txt "/* The local const declaration was lifted to top level */"
        elif v.IsParam then
            txt "/* The local param declaration was lifted to top level */"
        else
            // Otherwise this Blech variable is mutable or immutable (let), and it becomes a static variable in C
            // interface of current activity is updated
            let newIface = Compilation.addLocal (!curComp) {pos = v.pos; name = v.name; datatype = v.datatype; isMutable = true; allReferences = HashSet()}
            curComp := newIface
            // make sure the prev variable is initialised as well (if it exists) - this is crucial if the prev value is used in the same block where the variable is declared
            let prevInit =
                if List.contains v.name (!curComp).varsToPrev then
                    cpAssignDefaultPrevInActivity ctx.tcc v.name
                else
                    empty
            // rewrite into assignment
            let norm =
                normaliseVarDecl ctx.tcc v
                |> List.map (function 
                    | Stmt.Assign(_, lhs, rhs) -> cpAssign ctx.tcc lhs rhs
                    | _ -> failwith "Must be an assignment here!") // not nice
            // zero out everything that is not set explicitly
            let reinit =
                match v.datatype with
                | ValueTypes (ValueTypes.StructType _)
                | ValueTypes (ArrayType _) ->
                    let lhs =
                        { lhs = LhsCur(TypedMemLoc.Loc v.name)
                          typ = v.datatype
                          range = v.pos }
                    nullify ctx.tcc lhs
                | _ -> empty
            reinit :: norm @ [prevInit] |> dpBlock

    | Action.ExternalVarDecl v ->
        if List.contains v.name (!curComp).varsToPrev then
            // Dually to local variables--prev on external variables are 
            // generated as static C variables and thus added to the local interface here
            let prevName = {v.name with prefix = "blech_prev" :: v.name.prefix} // TODO hack, fix the string magic!
            let newIface = Compilation.addLocal (!curComp) {pos = v.pos; name = prevName; datatype = v.datatype; isMutable = true; allReferences = HashSet()}
            curComp := newIface
            // add new declaration to type check table
            TypeCheckContext.addDeclToLut ctx.tcc prevName (Declarable.ExternalVarDecl {v with name = prevName})
            // make sure the prev variable is initialised in the first reaction
            // this is crucial if the prev value is used in the same block where the variable is declared
            cpAssignDefaultPrevInActivity ctx.tcc v.name
        else
            // the external is used like a normal variable but in fact it is an auto C variable
            // initialisation happens in every reaction
            // the code for that is generated in function "translate" below
            txt "/* The extern declaration is outside the Blech code */"
                    
    | Action.Assign (r, lhs, rhs) -> cpAssign ctx.tcc lhs rhs
    | Action.Assert _
    | Action.Assume _ 
    | Action.Print _ ->
        failwith "Print, Assert, Assume not implemented yet."
    | Action.FunctionCall (r, whoToCall, inputs, outputs) ->
        cpFunctionCall ctx.tcc whoToCall inputs outputs
    | Action.Return (r, exprOpt) ->
        // note that the stoping of this activity is done in the calling processNode function
        match exprOpt with
        | None -> empty // control flow will end here - corresponds to a void return
        | Some expr ->
            // construct typed lhs
            let lhs =
                let name = (!curComp).retvar |> Option.get |> (fun p -> p.name)
                let typ =
                    match ctx.tcc.nameToDecl.[(!curComp).name] with
                    | FunctionPrototype p -> p.returns
                    | SubProgramDecl d -> d.returns
                    | _ -> failwith "expected subprogram, got something else"
                { lhs = LhsCur (TypedMemLoc.Loc name)
                  typ = ValueTypes typ
                  range = r }
            // call this function recursively with an Assign action
            cpAction ctx curComp (Action.Assign(r, lhs, expr))


let private cpResetPc tcc (pc: ParamDecl) =
    txt "BLC_SWITCH_TO_NEXTSTEP(" <^> cpPcName pc.name <^> txt ")" <^> semi

let private cpCopyInGlobal tcc (v: ExternalVarDecl) =
    let name = renderCName Current tcc v.name
    let extInit =
        v.annotation.TryGetCBinding
        |> Option.defaultValue "" //TODO: failwith or introduce errors in the code generation phase?
        |> txt
    match v.datatype with
    | ValueTypes (ArrayType _) ->
        let declare = cpArrayDeclDoc name v.datatype <^> semi
        let memcpy =
            txt "memcpy"
            <+> dpCommaSeparatedInParens
                [ name
                  extInit
                  sizeofMacro v.datatype ]
            <^> semi
        declare <..> memcpy
    | _ ->
        cpType v.datatype 
        <+> name <+> txt "=" 
        <+> extInit <^> semi

let private cpCopyOutGlobal tcc (v: ExternalVarDecl) =
    //let name = ppNameInActivity v.name
    let name = renderCName Current tcc v.name
    let extInit =
        v.annotation.TryGetCBinding
        |> Option.defaultValue "" //TODO: failwith or introduce errors in the code generation phase?
        |> txt
    match v.datatype with
    | ValueTypes (ArrayType _) ->
        let memcpy =
            txt "memcpy"
            <+> dpCommaSeparatedInParens
                [ extInit
                  name
                  sizeofMacro v.datatype ]
            <^> semi
        memcpy
    | _ ->
        extInit <+> txt "=" <+> name <^> semi


//=============================================================================
// Helpers for CodeGeneration - which return Docs
//=============================================================================

let private createPcName4node (node: Node) = "pc_" + string node.Payload.Thread.ID |> txt

let private findTreeFor (comp: Compilation) (node: Node) =
    let subTree = comp.GetActCtx.pcs.SubTreeForThread node.Payload.Thread
    assert subTree.IsSome
    subTree.Value

/// Returns the name of the program counter that the given node is executed under
// For this we use the thread ID of the node which is unique for all threads in one translation unit
let private pc4node comp node =
    let tree = findTreeFor comp node
    tree.mainpc.name.basicId

/// When accessing the pc, the context needs to be considered
// while pc4node gives just a name, this gives a Doc for the access
let private accessPC4node comp node =
    let tree = findTreeFor comp node
    cpPcName tree.mainpc.name

let private accessPC4block comp block =
    Seq.head block.innerNodes
    |> accessPC4node comp

let private initValue (ctx: TranslationContext) whoToCall = 
    let entry = ctx.pgs.[whoToCall].Entry
    ctx.bgs.[whoToCall].node2BlockNode.[entry].Payload.Priority

let private assignPc (pcDecl: ParamDecl) newVal =
    let nextStep = newVal |> string |> txt
    cpPcName pcDecl.name </> txt "=" </> nextStep <^> semi

let private advancePC (ctx: TranslationContext) comp source target =
    let newVal = ctx.bgs.[comp.name].node2BlockNode.[target].Payload.Priority
    let tree = findTreeFor comp source
    // note that for priority i, the pc is set to 2i
    assignPc tree.mainpc (2 * newVal)

let private endReaction comp source target =
    let newVal = target.Priority
    let tree = findTreeFor comp source
    // note that for termination in block i, the pc is set to 2i + 1
    assignPc tree.mainpc (2 * newVal + 1)

let private endThread comp node =
    let subTree = findTreeFor comp node
    subTree.AsList
    |> List.map (fun pcDecl -> assignPc pcDecl 0)
    |> dpBlock


let private areInSameBlock ctx actBeingTranslated n1 n2 =
    ctx.bgs.[actBeingTranslated].node2BlockNode.[n1] = ctx.bgs.[actBeingTranslated].node2BlockNode.[n2]
    // Note that this does not compare data of type Block but it compares data of type BlockNode
    // and does so by ReferenceEquality

let private getUniqueSuccBlock ctx actBeingTranslated node =
    let succs = ProgramGraph.cfSucc node
    if Seq.length succs = 1 then
        ctx.bgs.[actBeingTranslated].node2BlockNode.[Seq.head succs]
    else
        failwith "FAIL: expected exactly one successor"

let private getUniqueSuccNode node =
    let succs = ProgramGraph.cfSucc node
    if Seq.length succs = 1 then
        Seq.head succs
    else
        failwith "FAIL: expected exactly one successor"


let private findCompilationByName ctx compilations whoToCall =
    ctx.compilations @ compilations |> List.find (fun c -> c.name = whoToCall)

let private makeActCall ctx (compilations: Compilation list) (curComp: Compilation ref) (node: Node) pos pcName whoToCall receiverVar inputs outputs retcodeVar =
    let callee = findCompilationByName ctx compilations whoToCall
    // in case the return value is ignored with _
    // create a temporary variable to receive the value
    let receiver, receiverDecl =
        match callee.retvar, receiverVar with
        | Some r, None ->
            // calle does return something but no receiver var has been specified (_)
            // create dummy receiver variable
            let lhsName = mkIndexedAuxQNameFrom "receiverVar"
            let lhsTyp = r.datatype
            let tmpDecl = cpArrayDeclDoc (renderCName Current ctx.tcc lhsName) lhsTyp <^> semi
            let v = 
                { 
                    VarDecl.pos = range0
                    name = lhsName
                    datatype = lhsTyp
                    mutability = Mutability.Variable
                    initValue = {rhs = NatConst <| Constants.Nat.Zero8; typ = ValueTypes (NatType Nat8); range = pos} // that is a dummy/garbage
                    annotation = Attribute.VarDecl.Empty
                    allReferences = HashSet() 
                }
            TypeCheckContext.addDeclToLut ctx.tcc lhsName (Declarable.VarDecl v)
            let tmpLhs = Some {lhs = LhsCur (TypedMemLoc.Loc lhsName); typ = lhsTyp; range = range0} // range0 since it does not exist in original source code
            tmpLhs, [tmpDecl]
        | Some _, Some {lhs = ReturnVar} ->
            // caller does not store return value but immediately returns it further up the call chain
            let callerRetVar = Option.get (!curComp).retvar
            let returnLhs = Some { lhs = LhsCur (TypedMemLoc.Loc callerRetVar.name); typ = callerRetVar.datatype; range = callerRetVar.pos }
            returnLhs, []
        | Some _, Some _
            // caller receives the returned value in some receiver variable (cannot be wildcard at this point)
        | None, None ->
            // calle does not return anything and thus there is not receiver variable
            receiverVar, []
        | None, Some _ ->
            // this is unreachable
            // ruled out by type checker: calle returns nothing but caller provides a receiver
            failwith "Caller provides a receiver but there is nothing to be returned."

    let translatedCall = cpActivityCall ctx.tcc pcName callee.name inputs outputs receiver retcodeVar
    receiverDecl @ [translatedCall] |> dpBlock


let rec private processNode ctx (compilations: Compilation list) (curComp: Compilation ref) (node: Node) =
    match node.Payload.Typ with
    | HitAwaitLocation ->
        // advance counter
        let succ = getUniqueSuccBlock ctx (!curComp).name node
        endReaction !curComp node succ.Payload </> txt @"/* proceed from surface to depth */"
        // recursion ends here, since a HitAwait always ends a block
    
    | StartFromAwaitLocation -> // Here a reaction starts
        node.Outgoing
        |> Seq.toList
        |> List.sortBy(fun edge ->
            match edge.Payload with 
            | ControlFlow (Some (prio, guard)) -> prio
            | _ -> 0
            )
        |> List.rev // sort transitions by evaluation priority, highest first
        |> List.choose (fun edge ->
            match edge.Payload with 
            | ControlFlow (Some (_, guard)) -> // translate transitions
                let target = edge.Target
                let {prereqStmts=prereqStmts; cExpr=transCond} = cpExpr ctx.tcc guard
                let transBody = 
                    if areInSameBlock ctx (!curComp).name node target then
                        // if one unguarded transition, leading a node inside the same block, translate that node
                        processNode ctx compilations curComp target
                    else
                        // if one unguarded transition, that leaves block, advance pc
                        advancePC ctx !curComp node target
                Some (prereqStmts |> dpBlock, (transCond.Render, transBody))
            | _ -> None // discard ThreadConnect transitions that were introduced for proper scheduling
            )
        |> List.unzip
        ||> (fun a b -> dpBlock a, cpIfElseIf b)
        ||> (fun a b -> dpBlock [a;b])

        
    | ActionLocation action -> // Location that represents an atomic Blech statement
        match action with
        | Action.Return _ -> // special case: set main pc to 0 after setting the retvar and ignore successors
            [ cpAction ctx curComp action
              endThread !curComp node ]
            |> dpBlock
        | _ ->
            let succs = ProgramGraph.cfSucc node
            if Seq.isEmpty succs then
                cpAction ctx curComp action
            elif Seq.length succs = 1 then
                let target = Seq.head succs
                let transAction = cpAction ctx curComp action
                let transSucc =
                    if areInSameBlock ctx (!curComp).name node target then
                        // if one unguarded transition, leading a node inside the same block, translate that node
                        processNode ctx compilations curComp target
                    else
                        // if one unguarded transition, that leaves block, advance pc
                        advancePC ctx !curComp node target
                [transAction; transSucc] |> dpBlock
            else
                failwith "FAIL: an ActionLocation must have at most one successor"

    | GuardLocation ->
        // head of a loop or ITE or abort-after hook
        // translate to guarded assigments to pc
        match Seq.length node.Outgoing with
        | 0 -> // dead end, e.g. end of an activity, set pc = 0
            failwith "expected some transition transition out of guard location"
        | 1 -> // only one (true) transition, so behave like a normal location
            let edge = Seq.head node.Outgoing
            match edge.Payload with
            | ControlFlow _ 
            | ReturnFlow _ -> 
                let target = edge.Target
                if areInSameBlock ctx (!curComp).name node target then
                    // if one unguarded transition, leading a node inside the same block, translate that node
                    processNode ctx compilations curComp target
                else
                    // if one unguarded transition, that leaves block, advance pc
                    advancePC ctx !curComp node target
            | _ -> failwith "expected control flow transition" // Dataflow transitions are excluded by construction since they never emanate from nor point to simple Locations.
        | _ -> // at least two transitions into some blocks, ends this block
            node.Outgoing
            |> Seq.toList
            |> List.sortBy(fun edge ->
                match edge.Payload with 
                | ControlFlow (Some (prio, _))
                | ReturnFlow (prio, _) -> prio
                | _ -> 0
                )
            |> List.rev // sort transitions by evaluation priority, highest first
            |> List.choose (fun edge ->
                match edge.Payload with 
                | ControlFlow (Some (_, guard)) -> // translate transitions
                    let target = edge.Target
                    let {prereqStmts=prereqStmts; cExpr=transCond} = cpExpr ctx.tcc guard
                    let transBody = advancePC ctx !curComp node target
                    Some (prereqStmts |> dpBlock, (transCond.Render, transBody))
                | ReturnFlow (_, guard) ->
                    let target = edge.Target
                    let {prereqStmts=prereqStmts; cExpr=transCond} = cpExpr ctx.tcc guard
                    let loopHeadPc = advancePC ctx !curComp node target
                    let jump = txt "goto loopHead;"
                    let transBody = 
                        [ loopHeadPc
                          jump ]
                        |> dpBlock
                    Some (prereqStmts |> dpBlock, (transCond.Render, transBody))
                | _ -> None // never happens
                )
            |> List.unzip
            ||> (fun a b -> dpBlock a, cpIfElseIf b)
            ||> (fun a b -> dpBlock [a;b])
            // recursion ends here, since branching control flow ends a block

    | CobeginLocation joinNode ->
        // head of a cobegin
        ProgramGraph.cfSucc node
        |> Seq.map (fun target -> advancePC ctx !curComp target target) // this effectively initialises the subprograms pc to its first block
        |> Seq.append <| [advancePC ctx !curComp node joinNode] // set pc to join
        |> dpBlock
        
    | JoinLocation termVar ->
        // end of a cobegin
        // either the termination condition is fulfilled and we proceed to the exit
        // or it is not then we go the await location and check again in the next reaction

        // construct termination condition
        let prePCs =
            node.Incoming
            |> Seq.choose (fun edge -> 
                match edge.Payload with
                | TerminateThread strength -> Some (edge.Source, strength)
                | ControlFlow _ -> None
                | _ -> failwith "tick or data-flow edge enters join node, IMPOSSIBLE."
                )
        // are there strong threads?
        let strongThreads = prePCs |> Seq.filter (fun (_,strength) -> strength = Strong)
        let termCond = 
            if Seq.isEmpty strongThreads then
                // some weak has to finish
                prePCs
                |> Seq.map (fun (pc,_) -> accessPC4node !curComp pc <+> txt "== 0")
                |> punctuate (txt " ||")
                |> hsep
            else
                // all strong have to finish
                strongThreads
                |> Seq.map (fun (pc, _) -> accessPC4node !curComp pc <+> txt "== 0")
                |> punctuate (txt " &&")
                |> hsep
        // if true set all sub thread's pcs to 0 (to deactive them for future reactions)
        //         and proceed with next node
        let ifstmt =
            let deactivate = 
                prePCs 
                |> Seq.map (fun (pc,_) -> endThread !curComp pc)
                |> dpBlock
            let setTermVar = renderCName Current ctx.tcc termVar <+> txt "= 1" <^> semi
            let notTermVar = renderCName Current ctx.tcc termVar <+> txt "= 0" <^> semi
            cpIfElse termCond ([deactivate; setTermVar] |> dpBlock) notTermVar
        let declTermVar =
            let lhsTyp = ValueTypes(BoolType)
            cpType lhsTyp <+> renderCName Current ctx.tcc termVar <^> semi
        
        let nextStep =
            node.Outgoing
            |> Seq.toList
            |> List.sortBy(fun edge ->
                match edge.Payload with 
                | ControlFlow (Some (prio, guard)) -> prio
                | _ -> 0
                )
            |> List.rev // sort transitions by evaluation priority, highest first
            |> List.choose (fun edge ->
                match edge.Payload with 
                | ControlFlow (Some (_, guard)) -> // translate transitions
                    let target = edge.Target
                    let {prereqStmts=prereqStmts; cExpr=transCond} = cpExpr ctx.tcc guard
                    //let prereqStmts, transCond = cpExprInFunction ctx guard // cpExprInFunction -- evil hack to prevent dereferencing of automatic C variable
                    let transBody = advancePC ctx !curComp node target
                    Some (prereqStmts |> dpBlock, (transCond.Render, transBody))
                | _ -> None // never happens
                )
            |> List.unzip
            ||> (fun a b -> dpBlock a, cpIfElseIf b)
            ||> (fun a b -> dpBlock [a;b])
            
        [ declTermVar
          ifstmt
          nextStep ]
        |> dpBlock
                
    | AbortEnd innerDelayNodes -> // stop all subthreads and continue like a normal location
        // there should be one control flow successor
        let nextNode = getUniqueSuccNode node
        // test termination condition
        let thisThreadID = node.Payload.Thread.ID
        let prePCs =
            innerDelayNodes
            |> Seq.choose (fun n -> 
                if not (n.Payload.Thread.ID = thisThreadID) then Some n //(pc4node n)
                else None
                )
            |> Seq.distinct
        
        // set all sub thread's pcs to 0 (to deactive them for future reactions)
        //         and proceed with next node
        let codeDoc =
            let deactivate = 
                prePCs 
                |> Seq.map (fun pc -> endThread !curComp pc)
                |> dpBlock
            
            let transSucc = 
                if areInSameBlock ctx (!curComp).name node nextNode then
                    // if one unguarded transition, leading a node inside the same block, translate that node
                    processNode ctx compilations curComp nextNode
                else
                    // if one unguarded transition, that leaves block, advance pc
                    advancePC ctx !curComp node nextNode
            [deactivate; transSucc] |> dpBlock
        codeDoc </> txt @"/* abort subthreads and carry on */"

    | Location ->
        // an exit node
        match Seq.length (ProgramGraph.cfSucc node) with
        | 0 -> // dead end, e.g. end of an activity, set pc = 0
            endThread !curComp node <+> txt @"/* end */"
        | 1 ->
            let edge = 
                node.Outgoing
                |> Seq.filter ProgramGraph.isImmediateTransition
                |> Seq.head 
            match edge.Payload with
            | ControlFlow None -> 
                let target = edge.Target
                if areInSameBlock ctx (!curComp).name node target then
                    // if one unguarded transition, leading a node inside the same block, translate that node
                    processNode ctx compilations curComp target
                else
                    // if one unguarded transition, that leaves block, advance pc
                    advancePC ctx !curComp node target
            | TerminateThread _ -> // terminate thread
                endThread !curComp node <+> txt @"/* term */"
            | _ -> failwith "expected UNguarded transition" // Dataflow transitions are excluded by construction since they never emanate from nor point to simple Locations.
        | _ ->
            failwith "A simple location must have no more than one transition."

    // Initialise main program counter of callee
    // Perform the first call
    // and terminate execution for this thread, since the call cannot come back immediately according to Blech semantics
    | CallInit (pos, whoToCall, receiverVar, inputs, outputs, retcodeVar) ->
        let succ = getUniqueSuccNode node
        let thisNodePc = pc4node !curComp node
        let nextNodeStep =
            if areInSameBlock ctx (!curComp).name node succ then
                // if one unguarded transition, leading a node inside the same block, translate that node
                processNode ctx compilations curComp succ
            else
                // if one unguarded transition, that leaves block, advance pc
                advancePC ctx !curComp node succ
        
        // select callee's pcs from activity context and initialise them
        let callee = findCompilationByName ctx compilations whoToCall
        // add the PCs and locals of subprogram to this instance
        curComp := Compilation.addSubContext !curComp thisNodePc whoToCall callee.GetActCtx
        let calleesPCs = (!curComp).GetActCtx.subcontexts.[thisNodePc, whoToCall].pcs.AsList
        let prefixedPcs = calleesPCs |> List.map (fun p -> accessPC4node !curComp node <^> txt "_" <^> cpStaticName whoToCall <^> txt "." <^> txt p.name.basicId)
        let initCalleesPCs =
            match prefixedPcs with
            | mainpc :: otherPCs ->
                [
                    [mainpc </> txt "=" </> (2 * initValue ctx whoToCall |> string |> txt) <^> semi]
                    otherPCs |> List.map (fun pc -> pc </> txt "=" </> txt "0" <^> semi)
                ]
                |> List.concat
                |> dpBlock
            | _ -> failwith "A called activity needs to have at least one PC in its interface."

        let retcodeVarDoc =
            renderCName Current ctx.tcc retcodeVar
        let declRetcodeVar =
            let lhsTyp = ValueTypes(IntType Int32)
            cpType lhsTyp <+> retcodeVarDoc <^> semi
            
        // in case the return value is ignored with _
        // create a temporary variable to receive the value
        let translatedCall = makeActCall ctx compilations curComp node pos thisNodePc whoToCall receiverVar inputs outputs retcodeVar

        // suppress warning about set but unused value using a void cast with no effect
        let unused =
            txt "BLC_UNUSED" <^> parens retcodeVarDoc <^> semi
        
        dpBlock
        <| [ initCalleesPCs
             declRetcodeVar
             translatedCall
             unused
             nextNodeStep ]
        
    // Here we re-enter the run statement and continue execution of the subprogram
    | CallNode (pos, whoToCall, receiverVar, inputs, outputs, retcodeVar) ->
        let thisNodePc = pc4node !curComp node
        let nextStep =
            node.Outgoing
            |> Seq.toList
            |> List.sortBy(fun edge ->
                match edge.Payload with 
                | ControlFlow (Some (prio, guard)) -> prio
                | _ -> 0
                )
            |> List.rev // sort transitions by evaluation priority, highest first
            |> List.choose (fun edge ->
                match edge.Payload with 
                | ControlFlow (Some (_, guard)) -> // translate transitions
                    let target = edge.Target
                    //let prereqStmts, transCond = cpExprInFunction ctx guard // cpExprInFunction -- evil hack to prevent dereferencing of automatic C variable
                    let {prereqStmts=prereqStmts; cExpr=transCond} = cpExpr ctx.tcc guard
                    let transBody = advancePC ctx !curComp node target
                    Some (prereqStmts |> dpBlock, (transCond.Render, transBody))
                | _ -> None // never happens
                )
            |> List.unzip
            ||> (fun a b -> dpBlock a, cpIfElseIf b)
            ||> (fun a b -> dpBlock [a;b])
        
        let declRetcodeVar =
            let lhsTyp = ValueTypes(IntType Int32)
            cpType lhsTyp <+> renderCName Current ctx.tcc retcodeVar <^> semi

        let translatedCall = makeActCall ctx compilations curComp node pos thisNodePc whoToCall receiverVar inputs outputs retcodeVar

        let returnOrProceed = 
            match receiverVar with
            | Some {lhs = ReturnVar} -> // return run... end this thread
                // if (0 == retcode) {end thread} else {nextStep}
                let hasActTerminated = txt "0 ==" <+> renderCName Current ctx.tcc retcodeVar
                cpIfElse hasActTerminated (endThread !curComp node) nextStep
            | _ -> // normal run... proceed to the next block
                nextStep

        dpBlock
        <| [ declRetcodeVar
             translatedCall
             returnOrProceed ]

let private translateBlock ctx compilations curComp block =
    // traverse subgraph
    // at each location perform the required action, then traverse all outgoing CONTROL FLOW edges and (respecting the guards)
    // perform the next action or set the pc
    // note that due to current block construction, each block contains only a sequence, branching control flow can only occur at the last (exit) node
    let prioAsPc = 2 * block.Priority |> string |> txt
    let cond = accessPC4block !curComp block <+> txt "==" <+> prioAsPc
    let body = processNode ctx compilations curComp block.innerNodes.[0]
    cpIfOnly cond body

/// Extract all QNames of variables that require a prev location in given code
//let private collectVarsToPrev body =
//    let rec processExpr expr =
//        match expr.rhs with
//        // locations
//        | RhsCur tml ->
//            tml.FindAllIndexExpr
//            |> List.fold (fun processedExprs nextSubExpr -> processedExprs @ processExpr nextSubExpr) []
//        | RhsStructure.Prev tml->
//            tml.FindAllIndexExpr
//            |> List.fold (fun processedExprs nextSubExpr -> processedExprs @ processExpr nextSubExpr) []
//            |> (@) <| [tml.QNamePrefix]
//        // call
//        | FunCall (_, inputs, _) ->
//            inputs |> List.map processExpr |> List.concat   
//        // constants and literals
//        | BoolConst _
//        | IntConst _
//        | FloatConst _
//        | ResetConst -> []
//        | StructConst fields ->
//            fields |> List.map (fun (_,e) -> processExpr e) |> List.concat   
//        | ArrayConst fields ->
//            fields |> List.map (fun (_,e) -> processExpr e) |> List.concat   
//        // boolean
//        | Neg e -> processExpr e
//        | Conj (e1, e2) 
//        | Disj (e1, e2) 
//        | Xor (e1, e2) 
//        // relations
//        | Les (e1, e2) 
//        | Leq (e1, e2) 
//        | Equ (e1, e2) 
//        // arithmetic
//        | Add (e1, e2) 
//        | Sub (e1, e2) 
//        | Mul (e1, e2) 
//        | Div (e1, e2) 
//        | Mod (e1, e2) -> processExpr e1 @ processExpr e2
        
//    let rec processStmt stmt =
//        match stmt with
//        // calling
//        | Stmt.FunctionCall (_, _, inputs, _)
//        | ActivityCall (_, _, _, inputs, _) ->
//            inputs |> List.map processExpr |> List.concat   
//        | Stmt.Return (_, exprOpt) ->
//            exprOpt 
//            |> function
//            | None -> []
//            | Some l -> processExpr l
//        // actions
//        | Stmt.VarDecl v ->
//            processExpr v.initValue
//        | Stmt.Assert _ // ignore assert, assume and print
//        | Stmt.Assume _
//        | Stmt.Print _ -> []
//        | Stmt.Await (_, expr) 
//        | Stmt.Assign (_, _, expr) ->
//            processExpr expr
//        //recurse
//        | ITE (_, c, ifBranch, elseBranch) ->
//            processExpr c
//            @ List.concat (List.map processStmt ifBranch)
//            @ List.concat (List.map processStmt elseBranch)
//        | Cobegin (_, blocks) ->
//            blocks 
//            |> List.map (fun (_, body) -> (body |> List.map processStmt |> List.concat)) 
//            |> List.concat    
//        | WhileRepeat (_, c, body) 
//        | RepeatUntil (_, body, c, _)
//        | Preempt (_, _, c, _, body) ->
//            processExpr c
//            @ List.concat (List.map processStmt body)
//        // scoping
//        | StmtSequence stmts ->
//            stmts |> List.map processStmt |> List.concat

//    body |> List.map processStmt |> List.concat |> List.distinct

/// Extract all QNames of variables that require a prev location in given code
// runs on nodes and program graphs instead of statements
// became necessary when strong abort was translated by introducing a prev on the condition and thus deviating from given source code
// might change again
let private collectVarsToPrev2 pg =
    let rec processLhs lhs =
        match lhs.lhs with
        | Wildcard -> []
        | ReturnVar -> []
        | LhsCur tml
        | LhsNext tml ->
            tml.FindAllIndexExpr
            |> List.fold (fun processedExprs nextSubExpr -> processedExprs @ processExpr nextSubExpr) []
    and processExpr expr =
        match expr.rhs with
        // locations
        | RhsCur tml ->
            tml.FindAllIndexExpr
            |> List.fold (fun processedExprs nextSubExpr -> processedExprs @ processExpr nextSubExpr) []
        | RhsStructure.Prev tml->
            tml.FindAllIndexExpr
            |> List.fold (fun processedExprs nextSubExpr -> processedExprs @ processExpr nextSubExpr) []
            |> (@) <| [tml.QNamePrefix]
        // call
        | FunCall (_, inputs, outputs) ->
            (inputs |> List.map processExpr |> List.concat)
            @ (outputs |> List.map processLhs |> List.concat)
        // constants and literals
        | BoolConst _
        | IntConst _
        | NatConst _
        | BitsConst _ 
        | FloatConst _
        | ResetConst -> []
        | StructConst fields ->
            fields |> List.map (fun (_,e) -> processExpr e) |> List.concat   
        | ArrayConst fields ->
            fields |> List.map (fun (_,e) -> processExpr e) |> List.concat   
        // type conversion
        | Convert (e, _, _) -> processExpr e
        // boolean
        | Neg e -> processExpr e
        | Bnot e -> processExpr e
        | Conj (e1, e2) 
        | Disj (e1, e2) 
        // relations
        | Les (e1, e2) 
        | Leq (e1, e2) 
        | Equ (e1, e2) 
        // arithmetic
        | Add (e1, e2) 
        | Sub (e1, e2) 
        | Mul (e1, e2) 
        | Div (e1, e2) 
        | Mod (e1, e2) 
        // bitwise
        | Band (e1, e2)
        | Bor (e1, e2)
        | Bxor (e1, e2)
        | Shl (e1, e2)
        | Shr (e1, e2)
        | Sshr (e1, e2)
        | Rotr (e1, e2)
        | Rotl (e1, e2) -> processExpr e1 @ processExpr e2
            
    let rec processNode (node: Node) =
        match node.Payload.Typ with
        | ActionLocation action ->
            match action with
            | Nothing -> []
            | ExternalVarDecl _ -> [] // has not init value, if prev'ed it appears in some rhs
            | VarDecl v -> processExpr v.initValue
            | Assert (_, expr, _)
            | Assume (_, expr, _)
            | Assign (_, _, expr) -> processExpr expr
            | Print (_, _, exprs) -> exprs |> List.map processExpr |> List.concat
            | FunctionCall (_, _, inputs, _) ->
                inputs |> List.map processExpr |> List.concat   
            | Return (_, exprOpt) ->
                exprOpt |> Option.toList |> List.map processExpr |> List.concat
        | CallInit (_, _, _, inputs, _, _) 
        | CallNode (_, _, _, inputs, _, _) ->
            inputs |> List.map processExpr |> List.concat   
        | HitAwaitLocation 
        | StartFromAwaitLocation
        | Location 
        | AbortEnd _
        | GuardLocation
        | CobeginLocation _
        | JoinLocation _ -> []

    let rec processEdge (edge: Blech.Intermediate.Edge) =
        match edge.Payload with
        | ControlFlow optGuard ->
            optGuard |> Option.toList |> List.unzip |> snd |> List.map processExpr |> List.concat
        | ReturnFlow guard ->
            [guard] |> List.unzip |> snd |> List.map processExpr |> List.concat
        | Tick _
        | DataFlow _
        | TerminateThread _ -> []
    
    (pg.Graph.Nodes |> Seq.toList |> List.map processNode |> List.concat)
    @ (pg.Graph.Edges |> Seq.toList |> List.map processEdge |> List.concat)
    |> List.distinct

let private translateActivity ctx compilations curComp (subProgDecl: SubProgramDecl) =
    let addPc _ (node : Node) =
        let pc =
            { name = mkAuxQNameFrom <| render None (createPcName4node node)
              pos = range0
              datatype = ValueTypes (NatType Nat32)
              isMutable = true
              allReferences = HashSet() }
        curComp := Compilation.addPc !curComp node.Payload.Thread pc
        false
    let name = subProgDecl.name
    curComp := { !curComp with varsToPrev = collectVarsToPrev2 ctx.pgs.[name] }
    // build pc tree by traversing the program graph and create a pc per thread
    let progGraph = ctx.pgs.[name]
    let aborted = GenericGraph.depthsFirstForward [progGraph.Entry] addPc GenericGraph.proceed GenericGraph.proceed GenericGraph.proceed
    assert not aborted
    let blockGraph = ctx.bgs.[name].blockGraph
    // perform scheduling (i.e. compute block priorities)
    BlockGraph.assignPriorities blockGraph
    Logging.log4 "translateActivity" ("scheduled graph\n" + blockGraph.ToString())
    // translate block by block
    blockGraph.Nodes
    |> Seq.toList
    |> List.sortBy (fun bn -> bn.Payload.Priority)
    |> List.map (fun bn -> translateBlock ctx compilations curComp bn.Payload) 
    // return C source code


let private pcInit ctx prefix (comp: Compilation) =
    // TODO passing the "blc_blech_ctx. or ->" as a string seems unclean, fg 12.10.20
    let mainPc = txt prefix <^> txt comp.GetActCtx.pcs.mainpc.name.basicId
    let initVal = initValue ctx comp.name
    let initVal2 = 2 * initVal |> string |> txt
    mainPc <+> txt "=" <+> initVal2 <^> semi // assignPC won't work here, mind the level of indirection!
    |> cpIndent

/// Generate statements which initialises program counters 
/// used in the init function
let internal mainPCinit ctx (entryCompilation: Compilation) =
    pcInit ctx "blc_blech_ctx." entryCompilation


/// Given a translation context, a list of produced compilations so far,
/// and an activity, produce a Compilation for that activity.
let internal translate ctx compilations (subProgDecl: SubProgramDecl) =
    // for an activity, translate its graph
    // while doing so collect all local variables, pcs
    // wrap code in function that expects values for all
    // ins, outs, globals, locals, pcs
    let name = subProgDecl.name
    // generate a retvar if the activity is non-void
    let retvar =
        if subProgDecl.returns = Void then
            None
        else
            let qname = QName.Create subProgDecl.name.moduleName (subProgDecl.name.prefix @ [subProgDecl.name.basicId]) "retvar" Dynamic
            let v = { name = qname
                      pos = subProgDecl.pos
                      datatype = ValueTypes subProgDecl.returns
                      isMutable = true 
                      allReferences = HashSet() }
            TypeCheckContext.addDeclToLut ctx.tcc qname (Declarable.ParamDecl v)
            Some v
    
    let curComp = ref {Compilation.mkNew name with inputs = subProgDecl.inputs; outputs = subProgDecl.outputs; retvar = retvar}
        
    let code = translateActivity ctx compilations curComp subProgDecl

    let resetPCs =
        (!curComp).GetActCtx.pcs.AsList
        |> List.map (cpResetPc ctx.tcc)
        |> dpBlock

    let returnPC =
        let mainpc =
            (!curComp).GetActCtx.pcs.mainpc.name
            |> cpPcName
        txt "return" <+> mainpc <+> semi

    // copy-in external var/let
    let copyIn =
        subProgDecl.globalInputs @ subProgDecl.globalOutputsInScope
        |> List.map (cpCopyInGlobal ctx.tcc)
        |> dpBlock

    // write extern var back to environment
    let copyOut =
        subProgDecl.globalOutputsInScope
        |> List.map (cpCopyOutGlobal ctx.tcc)
        |> dpBlock

    // initially declare variables and set the to the "previous" value
    let setPrevVars =
        let takeOnlyLocal qn =
            // exclude ExternVarDecl since they are generated as automatic C vars
            match ctx.tcc.nameToDecl.[qn] with
            | Declarable.ExternalVarDecl _ -> false
            | _ -> true // there may be local, Backend-generated prev vars which are not in tcc
        (!curComp).varsToPrev
        |> Seq.filter takeOnlyLocal
        |> Seq.map (cpAssignPrevInActivity ctx.tcc)
        |> dpBlock

    let setExternPrevVars =
        let takeOnlyExtern qn =
            match ctx.tcc.nameToDecl.[qn] with
            | Declarable.ExternalVarDecl _ -> Some qn
            | _ -> None
        (!curComp).varsToPrev
        |> Seq.choose takeOnlyExtern
        |> Seq.map (cpAssignDefaultPrevInActivity ctx.tcc)
        |> dpBlock

    // insert val declarations and prev updates
    let completeBody = 
        let hasReturnFlow =
            ctx.pgs.[name].Graph.Edges
            |> Seq.exists (fun edge -> match edge.Payload with | ReturnFlow _ -> true | _ -> false)
        match code with
        | []
        | [_] -> failwith "An activity must have a non-empty body with at least one await."
        | initBlock :: rest -> 
            copyIn 
            :: setPrevVars 
            :: (if hasReturnFlow then txt "loopHead:" else empty) // avoid C compiler warning about unused labels
            :: initBlock 
            :: rest 
            |> dpBlock

    let initBody = pcInit ctx "blc_blech_ctx->" !curComp

    let initActivityCode =
        txt "void"
        <+> cpStaticName (!curComp).name <^> txt "_init"
        <+> cpIface ctx.tcc (!curComp)
        <+> txt "{"
        <.> cpIndent initBody // set main pc to 0
        <.> txt "}"

    let completeActivityCode =
        txt "blc_pc_t"
        <+> cpStaticName (!curComp).name
        <+> cpIface ctx.tcc (!curComp)
        <+> txt "{"
        <.> cpIndent completeBody
        <.> cpIndent setExternPrevVars // prev on extern is set AT THE END of the reaction
        <.> cpIndent copyOut
        <.> cpIndent resetPCs
        <.> cpIndent returnPC
        <.> txt "}"

    let signature =
        txt "blc_pc_t"
        <+> cpStaticName (!curComp).name
        <+> cpIface ctx.tcc (!curComp)
        <^> semi
        
    let optDoc = 
        cpOptDocComments subProgDecl.annotation.doc

    let initAndStep =
        [ initActivityCode
          empty // insert empty line in between
          completeActivityCode ]
        |> vsep

    curComp := { !curComp
                 with 
                    signature = signature
                    implementation = initAndStep
                    doc = optDoc }
    !curComp