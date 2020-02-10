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
open Compilation
open CPdataAccess
open CPrinter


let private setExternPrevForNextReaction ctx (v: ExternalVarDecl) =
    let prevName = {v.name with basicId = "prev_"+v.name.basicId}
    let name = ppNameInActivity prevName
    match v.datatype with
    | ValueTypes (ArrayType _) ->
        let prereqStmts, processedContainer = cpRhsInActivity ctx (RhsCur (Loc v.name))
        let cpy = 
            txt "memcpy"
            <^> dpCommaSeparatedInParens
                [ name
                  processedContainer
                  sizeofMacro v.datatype ]
            <^> semi
        prereqStmts @ [cpy] |> dpBlock
    | _ ->
        let value = ppNameInActivity v.name
        txt "*" <^> name <+> txt "=" <+> value <^> semi

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
            let newIface = Iface.addLocals (!curComp).iface {pos = v.pos; name = v.name; datatype = v.datatype; isMutable = true; allReferences = HashSet()}
            curComp := {!curComp with iface = newIface}
            // make sure the prev variable is initialised as well (if it exists) - this is crucial if the prev value is used in the same block where the variable is declared
            let prevInit =
                if List.contains v.name (!curComp).varsToPrev then
                    match v.datatype with
                    | ValueTypes (ArrayType _) ->
                        let name = ppPrevName v.name
                        let prereqStmts, processedContainer = cpRhsInActivity ctx (RhsCur (Loc v.name))
                        let cpy = 
                            txt "memcpy"
                            <^> dpCommaSeparatedInParens
                                [ name
                                  processedContainer
                                  sizeofMacro v.datatype ]
                            <^> semi
                        prereqStmts @ [cpy] |> dpBlock
                    | _ -> cpAssignDefaultPrevInActivity ctx v.name
                else
                    empty
            // rewrite into assignment
            let norm =
                normaliseVarDecl ctx.tcc v
                |> List.map (function 
                    | Stmt.Assign(_, lhs, rhs) -> 
                        match lhs.typ with
                        | ValueTypes (ArrayType _) ->
                            cpMemCpyArr false ctx lhs.lhs rhs
                        | _ ->
                            cpAssignInActivity ctx lhs.lhs rhs
                    | _ -> failwith "Must be an assignment here!") // not nice
            // zero out everything that is not set explicitly
            let reinit =
                match v.datatype with
                | ValueTypes (ValueTypes.StructType _)
                | ValueTypes (ArrayType _) ->
                    cpMemSet false ctx {lhs = LhsCur(Loc v.name); typ = v.datatype; range = v.pos}
                | _ -> empty
            reinit :: norm @ [prevInit] |> dpBlock

    | Action.ExternalVarDecl v ->
        if List.contains v.name (!curComp).varsToPrev then
            // Dually to local variables--prev on external variables are 
            // generated as static C variables and thus added to the local interface here
            let prevName = {v.name with basicId = "prev_"+v.name.basicId}
            let newIface = Iface.addLocals (!curComp).iface {pos = v.pos; name = prevName; datatype = v.datatype; isMutable = true; allReferences = HashSet()}
            curComp := {!curComp with iface = newIface}
            // make sure the prev variable is initialised in the first reaction
            // this is crucial if the prev value is used in the same block where the variable is declared
            setExternPrevForNextReaction ctx v
                
        else
            // the external is used like a normal variable but in fact it is an auto C variable
            // initialisation happens in every reaction
            // the code for that is generated in function "translate" below
            txt "/* The extern declaration is outside the Blech code */"
                    
    | Action.Assign (r, lhs, rhs) ->
        let norm =
            normaliseAssign ctx.tcc (r, lhs, rhs)
            |> List.map (function 
                | Stmt.Assign(_, lhs, rhs) -> 
                    match lhs.typ with
                    | ValueTypes (ArrayType _) ->
                        cpMemCpyArr false ctx lhs.lhs rhs
                    | _ ->
                        cpAssignInActivity ctx lhs.lhs rhs
                | _ -> failwith "Must be an assignment here!") // not nice
        
        match rhs.rhs with
        | StructConst _
        | ArrayConst _ when isLiteral rhs->
            // re-initialise the whole blob and then set the given fields
            let reinit = cpMemSet false ctx lhs
            reinit :: norm |> dpBlock
        | _ ->
            let prereqStmts, transExpr = makeTmpForComplexConst false ctx rhs 
            match transExpr with
            | Orig _ -> 
                match lhs.typ with
                | ValueTypes (ArrayType _) -> // a = b; where the variables are arrays
                    cpMemCpyArr false ctx lhs.lhs rhs
                | _ ->
                    cpAssignInActivity ctx lhs.lhs rhs
            | Done d ->
                let cpy = cpMemCpyDoc false ctx lhs d
                prereqStmts @ [cpy] |> dpBlock
    | Action.Assert _
    | Action.Assume _ 
    | Action.Print _ ->
        //[
        //    [txt formatstr]
        //    exprs |> List.map (cpExprInActivity ctx curComp)
        //]
        //|> List.concat
        //|> ppComSepInParens
        //|> (<^>) (txt "printf")
        //|> (<^>) <| semi
        failwith "Print, Assert, Assume not implemented yet."
    | Action.FunctionCall (r, whoToCall, inputs, outputs) ->
        // Since function calls statements and expressions are translated in the same way
        // simply call the expression translation here
        let prereqStmts, processedCall =
            {rhs = FunCall (whoToCall, inputs, outputs); typ = Types.ValueTypes Void; range = r}
            |> cpExprInActivity ctx
        prereqStmts @ [ processedCall <^> semi ]
        |> dpBlock
    | Action.Return (r, exprOpt) ->
        // note that the stoping of this activity is done in the calling processNode function
        match exprOpt with
        | None -> empty // control flow will end here - corresponds to a void return
        | Some expr ->
            // construct typed lhs
            let lhs =
                let name = (!curComp).iface.retvar |> Option.get |> (fun p -> p.name)
                let typ =
                    match ctx.tcc.nameToDecl.[(!curComp).name] with
                    | FunctionPrototype p -> p.returns
                    | SubProgramDecl d -> d.returns
                    | _ -> failwith "expected subprogram, got something else"
                { lhs = LhsCur (Loc name)
                  typ = ValueTypes typ
                  range = r }
            // call this function recursively with an Assign action
            cpAction ctx curComp (Action.Assign(r, lhs, expr))

let private cpActCall ctx whoToCall inputs outputs locals pcs receiverVar isDummy tempVarName =
    //let prefix doc = if isDummy then txt "&" <^> doc else doc
    let prereqStmtsLst, transInputs = 
        inputs
        |> List.map (makeTmpForComplexConst false ctx)
        |> List.unzip
    let inputPrereq, processedInputs = 
        transInputs
        |> List.map (function
            | Orig input -> cpInputArgInSubprogram false ctx input
            | TransExpr.Done d -> [], d)
        |> List.unzip
    let outputPrereq, processedOutputs = 
        outputs
        |> List.map (fun l -> cpOutputArgInActivity ctx l.lhs)
        |> List.unzip
    let localsPrereq, processedLocals = 
        locals 
        |> List.map (fun l -> cpOutputArgInActivity ctx l.lhs)
        |> List.unzip
    let pcPrereq, processedPcs = // this should not do anything
        pcs 
        |> List.map (fun l -> cpOutputArgInActivity ctx l.lhs)
        |> List.unzip
    let retPrereq, processedRet =
        receiverVar
        |> Option.toList 
        |> List.map (fun l -> if isDummy then CPdataAccess.cpOutputArgInFunction ctx l.lhs else cpOutputArgInActivity ctx l.lhs) // again monster hack for auxiliary locations in activities, cf. 
        //|> List.map (fun (f, s) -> f, prefix s)
        |> List.unzip

    let actCall = 
        [
            processedInputs
            processedOutputs
            processedLocals
            processedPcs
            processedRet
        ]
        |> List.concat
        |> dpCommaSeparatedInParens
        |> (<^>) (ppName whoToCall)
    
    prereqStmtsLst @ inputPrereq @ outputPrereq @ localsPrereq @ pcPrereq @ retPrereq |> List.concat, ppName tempVarName <+> txt "=" <+> actCall <^> semi

let private cpResetPc (pc: ParamDecl) =
    let ppPc = cpDeref (ppName pc.name)
    txt "BLC_SWITCH_TO_NEXTSTEP(" <^> ppPc <^> txt ")" <^> semi

let private cpCopyInGlobal (v: ExternalVarDecl) =
    let name = ppNameInActivity v.name
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

let private cpCopyOutGlobal (v: ExternalVarDecl) =
    let name = ppNameInActivity v.name
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

/// Returns the name of the program counter that the given node is executed under
// For this we use the thread ID of the node which is unique for all threads in one translation unit
let private pc4node (node: Node) = "pc_" + string node.Payload.Thread.ID |> txt

/// Returns the name of the program counter that the given block is executed under
// Relies on the fact that all nodes of a BlockNode have the same thread ID and thus the same pc.
let private pc4block (block: Block) = Seq.head block.innerNodes |> pc4node

let private initValue (ctx: TranslationContext) whoToCall = 
    let entry = ctx.pgs.[whoToCall].Entry
    ctx.bgs.[whoToCall].node2BlockNode.[entry].Payload.Priority

let getMainPCinBG (compilations: Compilation list) name =
    compilations
    |> List.find (fun c -> c.name = name) // TODO: expensive
    |> (fun c -> c.iface.pcs.Head.name)
    |> ppName

let private assignPc pc newVal =
    let nextStep = newVal |> string |> txt
    cpDeref pc </> txt "=" </> nextStep <^> semi

let private advancePC (ctx: TranslationContext) actBeingTranslated source target =
    let newVal = ctx.bgs.[actBeingTranslated].node2BlockNode.[target].Payload.Priority
    // note that for priority i, the pc is set to 2i
    assignPc (pc4node source) (2 * newVal)

let private endReaction source target =
    let newVal = target.Priority
    // note that for termination in block i, the pc is set to 2i + 1
    assignPc (pc4node source) (2 * newVal + 1)

let private endThread node = assignPc (pc4node node) 0

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

let private makeActCall ctx (compilations: Compilation list) (curComp: Compilation ref) (node: Node) pos whoToCall receiverVar inputs outputs tempVarName =
    // add the PCs and locals of subprogram to this instance
    let callee = compilations |> List.find (fun c -> c.name = whoToCall) // TODO: expensive
    let prefIface = includeIface (pc4node node) curComp callee
    prefIface.pcs @ prefIface.locals
    |> List.iter (fun pc ->
        try ctx.tcc.nameToDecl.Add(pc.name, Declarable.ParamDecl pc)
        with _ -> () // if this pc is already in there, nothing to do
        )
    let lhsLocals = prefIface.locals |> List.map (fun p -> {lhs = LhsCur (Loc p.name); typ = p.datatype; range = range0}) // range0 since they do not exist in original source code
    let lhsPcs = prefIface.pcs |> List.map (fun p -> {lhs = LhsCur (Loc p.name); typ = p.datatype; range = range0}) // range0 since they do not exist in original source code
    // in case the return value is ignored with _
    // create a temporary variable to receive the value
    match callee.iface.retvar, receiverVar with
    | Some r, None ->
        let lhsName = mkIndexedAuxQNameFrom "receiverVar"
        let lhsTyp = r.datatype
        let tmpDecl = cpArrayDeclDoc (ppName lhsName) lhsTyp <^> semi
        let v = 
            { 
                VarDecl.pos = range0
                name = lhsName
                datatype = lhsTyp
                mutability = Mutability.Variable
                initValue = {rhs = IntConst 0I; typ = Types.ValueTypes (UintType Uint8); range = pos} // that is garbage
                annotation = Attribute.VarDecl.Empty
                allReferences = HashSet() 
            }
        TypeCheckContext.addDeclToLut ctx.tcc lhsName (Declarable.VarDecl v)
        let tmpLhs = Some {lhs = LhsCur (Loc lhsName); typ = lhsTyp; range = range0} // range0 since it does not exist in original source code
        let prereqStmts, translatedCall = cpActCall ctx callee.name inputs outputs lhsLocals lhsPcs tmpLhs true tempVarName
        prereqStmts @ [tmpDecl] |> dpBlock, translatedCall
    | _ -> 
        let prereqStmts, translatedCall = cpActCall ctx callee.name inputs outputs lhsLocals lhsPcs receiverVar false tempVarName
        prereqStmts |> dpBlock, translatedCall


let rec private processNode ctx (compilations: Compilation list) (curComp: Compilation ref) (node: Node) =
    match node.Payload.Typ with
    | HitAwaitLocation ->
        // advance counter
        let succ = getUniqueSuccBlock ctx (!curComp).name node
        endReaction node succ.Payload </> txt @"/* proceed from surface to depth */"
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
                let prereqStmts, transCond = cpExprInActivity ctx guard
                let transBody = 
                    if areInSameBlock ctx (!curComp).name node target then
                        // if one unguarded transition, leading a node inside the same block, translate that node
                        processNode ctx compilations curComp target
                    else
                        // if one unguarded transition, that leaves block, advance pc
                        advancePC ctx (!curComp).name node target
                Some (prereqStmts |> dpBlock, (transCond, transBody))
            | _ -> None // discard ThreadConnect transitions that were introduced for proper scheduling
            )
        |> List.unzip
        ||> (fun a b -> dpBlock a, cpIfElseIf b)
        ||> (fun a b -> dpBlock [a;b])

        
    | ActionLocation action -> // Location that represents an atomic Blech statement
        match action with
        | Action.Return _ -> // special case: set main pc to 0 after setting the retvar and ignore successors
            [ cpAction ctx curComp action
              endThread node ]
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
                        advancePC ctx (!curComp).name node target
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
                    advancePC ctx (!curComp).name node target
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
                    let prereqStmts, transCond = cpExprInActivity ctx guard
                    let transBody = advancePC ctx (!curComp).name node target
                    Some (prereqStmts |> dpBlock, (transCond, transBody))
                | ReturnFlow (_, guard) ->
                    let target = edge.Target
                    let prereqStmts, transCond = cpExprInActivity ctx guard
                    let loopHeadPc = advancePC ctx (!curComp).name node target
                    let jump = txt "goto loopHead;"
                    let transBody = 
                        [ loopHeadPc
                          jump ]
                        |> dpBlock
                    Some (prereqStmts |> dpBlock, (transCond, transBody))
                | _ -> None // never happens
                )
            |> List.unzip
            ||> (fun a b -> dpBlock a, cpIfElseIf b)
            ||> (fun a b -> dpBlock [a;b])
            // recursion ends here, since branching control flow ends a block

    | CobeginLocation joinNode ->
        // head of a cobegin
        ProgramGraph.cfSucc node
        |> Seq.map (fun target -> advancePC ctx (!curComp).name target target) // this effectively initialises the subprograms pc to its first block
        |> Seq.append <| [advancePC ctx (!curComp).name node joinNode] // set pc to join
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
                | TerminateThread strength -> Some (pc4node edge.Source, strength)
                | ControlFlow _ -> None
                | _ -> failwith "tick or data-flow edge enters join node, IMPOSSIBLE."
                )
        // are there strong threads?
        let strongThreads = prePCs |> Seq.filter (fun (_,strength) -> strength = Strong)
        let termCond = 
            if Seq.isEmpty strongThreads then
                // some weak has to finish
                prePCs
                |> Seq.map (fun (pc,_) -> cpDeref pc <+> txt "== 0")
                |> punctuate (txt " ||")
                |> hsep
            else
                // all strong have to finish
                strongThreads
                |> Seq.map (fun (pc, _) -> cpDeref pc <+> txt "== 0")
                |> punctuate (txt " &&")
                |> hsep
        // if true set all sub thread's pcs to 0 (to deactive them for future reactions)
        //         and proceed with next node
        let ifstmt =
            let deactivate = 
                prePCs 
                |> Seq.map (fun (pc,_) -> assignPc pc 0) 
                |> dpBlock
            let setTermVar = ppName termVar <+> txt "= 1" <^> semi
            let notTermVar = ppName termVar <+> txt "= 0" <^> semi
            cpIfElse termCond ([deactivate; setTermVar] |> dpBlock) notTermVar
        let declTermVar =
            let lhsTyp = ValueTypes(BoolType)
            cpType lhsTyp <+> ppName termVar <^> semi
        
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
                    let prereqStmts, transCond = cpExprInFunction ctx guard // cpExprInFunction -- evil hack to prevent dereferencing of automatic C variable
                    let transBody = advancePC ctx (!curComp).name node target
                    Some (prereqStmts |> dpBlock, (transCond, transBody))
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
        let prePCs = Seq.distinct prePCs |> Seq.map pc4node
        
        // set all sub thread's pcs to 0 (to deactive them for future reactions)
        //         and proceed with next node
        let codeDoc =
            let deactivate = 
                prePCs 
                |> Seq.map (fun pc -> assignPc pc 0) 
                |> dpBlock
            
            let transSucc = 
                if areInSameBlock ctx (!curComp).name node nextNode then
                    // if one unguarded transition, leading a node inside the same block, translate that node
                    processNode ctx compilations curComp nextNode
                else
                    // if one unguarded transition, that leaves block, advance pc
                    advancePC ctx (!curComp).name node nextNode
            [deactivate; transSucc] |> dpBlock
        codeDoc </> txt @"/* abort subthreads and carry on */"

    | Location ->
        // an exit node
        match Seq.length node.Outgoing with
        | 0 -> // dead end, e.g. end of an activity, set pc = 0
            endThread node <+> txt @"/* end */"
        | 1 ->
            let edge = Seq.head node.Outgoing
            match edge.Payload with
            | ControlFlow None -> 
                let target = edge.Target
                if areInSameBlock ctx (!curComp).name node target then
                    // if one unguarded transition, leading a node inside the same block, translate that node
                    processNode ctx compilations curComp target
                else
                    // if one unguarded transition, that leaves block, advance pc
                    advancePC ctx (!curComp).name node target
            | TerminateThread _ -> // terminate thread
                endThread node <+> txt @"/* term */"
            | _ -> failwith "expected UNguarded transition" // Dataflow transitions are excluded by construction since they never emanate from nor point to simple Locations.
        | _ ->
            failwith "A simple location must have no more than one transition."

    // Initialise main program counter of callee
    // Perform the first call
    // and terminate execution for this thread, since the call cannot come back immediately according to Blech semantics
    | CallInit (pos, whoToCall, receiverVar, inputs, outputs, retcodeVar) ->
        let succ = getUniqueSuccNode node
        let nextNodeStep =
            if areInSameBlock ctx (!curComp).name node succ then
                // if one unguarded transition, leading a node inside the same block, translate that node
                processNode ctx compilations curComp succ
            else
                // if one unguarded transition, that leaves block, advance pc
                advancePC ctx (!curComp).name node succ
        // regarding names, we need instantiated names for pcs, locals and receiverVar of the called activity
        // obvious but stupid choice current pc + callinstance name + formal parameter name
        let callee = compilations |> List.find (fun c -> c.name = whoToCall) // TODO: expensive

        let pcPref = (pc4node node) |> render None
        let prefixedPcs =
            let mergePCAndWhoToCall (pc: ParamDecl) = 
                let prefix = pcPref :: whoToCall.toPrefix @ pc.name.prefix
                let id = pc.name.basicId
                QName.CreateAuxiliary prefix id
            callee.iface.pcs
            |> List.map mergePCAndWhoToCall  // merge whoToCall and pc
            |> List.map (fun pc -> ppName pc)
        let initCalleesPCs =
            match prefixedPcs with
            | mainpc :: otherPCs ->
                [
                    [assignPc mainpc (2 * initValue ctx whoToCall)]
                    otherPCs |> List.map (fun pc -> assignPc pc 0)
                ]
                |> List.concat
                |> dpBlock
            | _ -> failwith "A called activity needs to have at least one PC in its interface."

        let declRetcodeVar =
            let lhsTyp = ValueTypes(IntType Int32)
            cpType lhsTyp <+> ppName retcodeVar <^> semi
            
        // in case the return value is ignored with _
        // create a temporary variable to receive the value
        let tmpDecl, translatedCall = makeActCall ctx compilations curComp node pos whoToCall receiverVar inputs outputs retcodeVar
        
        dpBlock
        <| [ initCalleesPCs
             declRetcodeVar
             tmpDecl
             translatedCall
             nextNodeStep ]
        
    // Here we re-enter the run statement and continue execution of the subprogram
    | CallNode (pos, whoToCall, receiverVar, inputs, outputs, retcodeVar) ->
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
                    let prereqStmts, transCond = cpExprInFunction ctx guard // cpExprInFunction -- evil hack to prevent dereferencing of automatic C variable
                    let transBody = advancePC ctx (!curComp).name node target
                    Some (prereqStmts |> dpBlock, (transCond, transBody))
                | _ -> None // never happens
                )
            |> List.unzip
            ||> (fun a b -> dpBlock a, cpIfElseIf b)
            ||> (fun a b -> dpBlock [a;b])
        
        let declRetcodeVar =
            let lhsTyp = ValueTypes(IntType Int32)
            cpType lhsTyp <+> ppName retcodeVar <^> semi

        let tmpDecl, translatedCall = makeActCall ctx compilations curComp node pos whoToCall receiverVar inputs outputs retcodeVar
        
        dpBlock
        <| [ declRetcodeVar
             tmpDecl
             translatedCall
             nextStep ]

let private translateBlock ctx compilations curComp block =
    // traverse subgraph
    // at each location perform the required action, then traverse all outgoing CONTROL FLOW edges and (respecting the guards)
    // perform the next action or set the pc
    // note that due to current block construction, each block contains only a sequence, branching control flow can only occur at the last (exit) node
    let pc =
        { name = mkAuxQNameFrom <| render None (pc4block block)
          pos = range0
          datatype = Types.ValueTypes (UintType Uint32)
          isMutable = true
          allReferences = HashSet() }
    let newIface = Iface.addPcs (!curComp).iface pc
    let newLocalPcs = 
        (!curComp).localPcs 
        |> List.map (fun p -> p.name)
        |> List.contains pc.name
        |> function
            | true -> (!curComp).localPcs
            | false -> pc :: (!curComp).localPcs
    curComp := {!curComp with iface = newIface; localPcs = newLocalPcs}
    let prioAsPc = 2 * block.Priority |> string |> txt
    let cond = cpDeref (pc4block block) <+> txt "==" <+> prioAsPc
    let body = processNode ctx compilations curComp block.innerNodes.[0]
    cpIfOnly cond body // TODO: why do we need that, the body will contain an if statement with stricter conditions anyway?!

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
        | FloatConst _
        | ResetConst -> []
        | StructConst fields ->
            fields |> List.map (fun (_,e) -> processExpr e) |> List.concat   
        | ArrayConst fields ->
            fields |> List.map (fun (_,e) -> processExpr e) |> List.concat   
        // boolean
        | Neg e -> processExpr e
        | Conj (e1, e2) 
        | Disj (e1, e2) 
        | Xor (e1, e2) 
        // relations
        | Les (e1, e2) 
        | Leq (e1, e2) 
        | Equ (e1, e2) 
        // arithmetic
        | Add (e1, e2) 
        | Sub (e1, e2) 
        | Mul (e1, e2) 
        | Div (e1, e2) 
        | Mod (e1, e2) -> processExpr e1 @ processExpr e2
    
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
    let name = subProgDecl.name
    //curComp := { !curComp with varsToPrev = collectVarsToPrev subProgDecl.body }
    curComp := { !curComp with varsToPrev = collectVarsToPrev2 ctx.pgs.[name] }
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

    
/// Generate statements which initialises program counters 
/// used in the init function
let internal mainPCinit ctx compilations (entryCompilation: Compilation) =
    let mainPc = getMainPCinBG compilations entryCompilation.name
    let initVal = initValue ctx entryCompilation.name
    let initVal2 = 2 * initVal |> string |> txt
    mainPc <+> txt "=" <+> initVal2 <^> semi // assignPC won't work here, mind the level of indirection!
    |> cpIndent


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
                      datatype = Types.ValueTypes subProgDecl.returns
                      isMutable = true 
                      allReferences = HashSet() }
            TypeCheckContext.addDeclToLut ctx.tcc qname (Declarable.ParamDecl v)
            Some v
    
    let iface = {Iface.Empty with inputs = subProgDecl.inputs; outputs = subProgDecl.outputs; retvar = retvar}
    
    let curComp = ref {Compilation.Empty with name = name; iface = iface}
        
    let code = translateActivity ctx compilations curComp subProgDecl

    // if this is the entry point activity, add its iface variables to the 
    // type check context (as we do for activity calls)
    // this ensures that generated local variables (prev on extern) are add to 
    // the tcc.
    if subProgDecl.IsEntryPoint then
        (!curComp).iface.locals
        |> List.iter (fun localVar ->
            try ctx.tcc.nameToDecl.Add(localVar.name, Declarable.ParamDecl localVar)
            with _ -> () // if this pc is already in there, nothing to do
            )
    
    // start quick fix: make sure main pc is the first in !curComp.iface
    // this because we rely on the fact that the first pc is the main pc in various places
    
    let mainPC = pc4node ctx.pgs.[name].Entry |> render None
    
    let myCmp (p1: ParamDecl) (p2: ParamDecl) =
        if (p1.name.ToString()) = mainPC then -1
        elif (p2.name.ToString()) = mainPC then 1
        else 0
    
    let sortedPcs = List.sortWith myCmp (!curComp).iface.pcs
    
    curComp := {!curComp with iface = {(!curComp).iface with pcs = sortedPcs}}
    // end quick fix

    let resetPCs =
        (!curComp).localPcs
        |> List.map cpResetPc
        |> dpBlock

    let returnPC =
        // TODO: why is it so complicated? how does this relate to CPrinter.getMainPCinBG ?
        let mainpc =
            //ctx.bgs.[name].blockGraph.Nodes
            //|> Seq.toList
            //|> List.minBy (fun blockNode -> blockNode.Payload.Priority)
            let entry = ctx.pgs.[name].Entry
            ctx.bgs.[name].node2BlockNode.[entry]
            |> (fun x -> pc4block x.Payload)
        txt "return" <+> cpDeref mainpc <+> semi

    // copy-in external var/let
    let copyIn =
        subProgDecl.globalInputs @ subProgDecl.globalOutputsInScope
        |> List.map cpCopyInGlobal
        |> dpBlock

    // write extern var back to environment
    let copyOut =
        subProgDecl.globalOutputsInScope
        |> List.map cpCopyOutGlobal
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
        |> Seq.map (cpAssignPrevInActivity ctx)
        |> dpBlock

    let setExternPrevVars =
        let takeOnlyExtern qn =
            match ctx.tcc.nameToDecl.[qn] with
            | Declarable.ExternalVarDecl v -> Some v
            | _ -> None
        (!curComp).varsToPrev
        |> Seq.choose takeOnlyExtern
        |> Seq.map (setExternPrevForNextReaction ctx)
        |> dpBlock

    // insert val declarations and prev updates
    let completeBody = 
        match code with
        | []
        | [_] -> failwith "An activity must have a non-empty body with at least one await."
        | initBlock :: rest -> 
            copyIn :: setPrevVars :: txt "loopHead:" :: initBlock :: rest 
            |> dpBlock

    let completeActivityCode =
        txt "static" // TODO must be non-static if activity is exposed, fjg 17.01.19
        <+> txt "blc_pc_t"
        <+> ppName (!curComp).name
        <+> cpIface (!curComp).iface
        <+> txt "{"
        <.> cpIndent completeBody
        <.> cpIndent setExternPrevVars // prev on extern is set AT THE END of the reaction
        <.> cpIndent copyOut
        <.> cpIndent resetPCs
        <.> cpIndent returnPC
        <.> txt "}"

    let signature =
        txt "blc_pc_t"
        <+> ppName (!curComp).name
        <+> cpIface (!curComp).iface
        <^> semi
        
    let optDoc = 
        cpOptDocComments subProgDecl.annotation.doc

    curComp := { !curComp
                 with 
                    signature = signature
                    implementation = completeActivityCode
                    doc = optDoc }
    !curComp