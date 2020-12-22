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

module Blech.Frontend.TypeChecking

open System.Collections.Generic

open Blech.Common

open CommonTypes
open BlechTypes
open TyChecked
open TypeCheckContext
open TyChkAmendment
open TyChkExpressions

module Diagnostics = Blech.Common.Diagnostics
module Range = Blech.Common.Range


//=========================================================================
// Recursive helpers
//=========================================================================
type private StmtRetType =
    | NoReturn
    | May of ValueTypes
    | Must of ValueTypes


/// Determine the return type of a statement
let rec private stmtType stmt =
    match stmt with
    // atomic statements, except "return" and "run"
    | Stmt.VarDecl _ | Assign _ | Assert _ | Assume _ | Stmt.Print _ | Await _ 
    | Stmt.ExternalVarDecl _ | FunctionCall _ -> 
        Ok NoReturn
    // Must, if "return run"
    | ActivityCall (_, _, receiverOpt, _, _) ->
        match receiverOpt with
        | Some (ReturnLoc {typ = ValueTypes t}) -> Ok (Must t) // TODO: Restructure types, return should allow Value and Referencetypes, but no AnyTypes, fjg 2.7.20
        | _ -> Ok NoReturn
    // the "return" statement    
    | Return (pos, exprOpt) ->
        match exprOpt with 
        | Some expr ->
            match expr.typ with
            | ValueTypes t -> Must t |> Ok
            | _ -> Error [NonFirstClassReturnStmt pos]
        | None ->
            Must Void |> Ok
    // statements containing statements
    | WhileRepeat (_, _, body) ->
        stmtType (StmtSequence body)
        |> Result.map (function
            | NoReturn -> NoReturn
            | May t
            | Must t -> May t ) // may not return if cond is false and loop is skipped
    | RepeatUntil (_, body, _, _) ->
        stmtType (StmtSequence body)
    | Preempt (_, _, _, _, body) ->
        stmtType (StmtSequence body)
        |> Result.map (function
            | NoReturn -> NoReturn
            | May t
            | Must t -> May t) // body may not return when preempted
    | StmtSequence stmts ->
        let folder prev succ =
            prev |> Result.bind(fun okState ->
                match okState, succ with
                | NoReturn, _ -> Ok succ
                | Must _, _ -> prev
                | May _, NoReturn -> prev
                | May s, May e ->
                    if isLeftSupertypeOfRight (ValueTypes s) (ValueTypes e) then
                        prev
                    elif isLeftSupertypeOfRight (ValueTypes e) (ValueTypes s) then
                        Ok succ
                    else
                        Error [IncomparableReturnTypes(Range.range0, s, e)]
                | May s, Must e ->
                    if isLeftSupertypeOfRight (ValueTypes s) (ValueTypes e) then
                        Must s |> Ok
                    elif isLeftSupertypeOfRight (ValueTypes e) (ValueTypes s) then
                        Ok succ 
                    else
                        Error [IncomparableReturnTypes(Range.range0, s, e)]
            )
        stmts
        |> List.map stmtType
        |> contract
        |> Result.bind (List.fold folder (Ok NoReturn))
    | ITE (pos, _, ifBranch, elseBranch) ->
        stmtType (StmtSequence ifBranch)
        |> combine <| stmtType (StmtSequence elseBranch)
        |> Result.bind ( fun (ifType, elseType) ->
            match ifType, elseType with
            | NoReturn, NoReturn -> NoReturn |> Ok
            | NoReturn, May t
            | NoReturn, Must t
            | May t, NoReturn
            | Must t, NoReturn -> May t |> Ok
            | Must i, Must e ->
                if isLeftSupertypeOfRight (ValueTypes i) (ValueTypes e) then
                    Must i |> Ok
                elif isLeftSupertypeOfRight (ValueTypes e) (ValueTypes i) then
                    Must e |> Ok
                else
                    Error [IncomparableReturnTypes(pos, i, e)]
            | May i, Must e
            | Must i, May e
            | May i, May e ->
                if isLeftSupertypeOfRight (ValueTypes i) (ValueTypes e) then
                    May i |> Ok
                elif isLeftSupertypeOfRight (ValueTypes e) (ValueTypes i) then
                    May e |> Ok
                else
                    Error [IncomparableReturnTypes(pos, i, e)]
            )
    // We allow return statements only in the main thread of the activity,
    // i.e. never inside a cobegin statement
    | Cobegin (pos, blocks) ->
        let folder state elem =
            state |> Result.bind (fun stateRet ->
            match stateRet with
            | (May _)
            | (Must _) -> Error [ReturnsInCobegin pos]
            | (NoReturn) ->
                match elem with
                | (_, NoReturn) -> Ok NoReturn
                | _ -> Error [ReturnsInCobegin pos]
            )

        blocks
        |> List.map (fun (strength, stmts) -> stmtType (StmtSequence stmts) |> Result.map (fun x -> strength, x))
        |> contract
        |> Result.bind (List.fold folder (Ok NoReturn))
    
    
/// Check that if (and only if) the returns is non-void then every terminating run of the body must end in a return statement
/// and all return statements return a compatible type!
let private checkStmtsMatchReturn pos body retType =
    stmtType body
    |> Result.bind(function
        | NoReturn 
        | May Void ->
            if retType = Void then retType |> Ok
            else Error [MustReturnSomething (pos, retType)]
        | Must f ->
            if isLeftSupertypeOfRight (ValueTypes retType) (ValueTypes f) then Ok retType
            else Error [ReturnTypeMismatch (pos, ValueTypes retType, ValueTypes f)]
        | May f -> Error [MayOrMayNotReturn (pos, retType, f)]
        )


/// Checks whether the lists of statements does not contain any synchronous
/// statements. This check is required for function bodies.
let rec private checkAbsenceOfSyncStmts stmts = 
    let applyToList f =
        List.map f
        >> contract
        >> Result.bind (fun _ -> Ok ()) // in case we succeeded on every 
                                        // statement, simply indicate success
    let rec checkLhsRhs lhss rhss =
        let resIn = rhss |> applyToList checkAbsenceOfSyncExpr
        let checkLhs out =
            match out.lhs with
            | Wildcard -> Ok ()
            | ReturnVar -> Ok ()
            | LhsCur tml
            | LhsNext tml ->
                tml.FindAllIndexExpr
                |> applyToList checkAbsenceOfSyncExpr
        let resOut = lhss |> applyToList checkLhs
        [resIn; resOut] |> applyToList id
    and checkAbsenceOfSyncExpr expr =
        match expr.rhs with
        | Prev _ -> Error [PrevInFunction expr.Range]
        | RhsCur tml ->
            tml.FindAllIndexExpr
            |> applyToList checkAbsenceOfSyncExpr
        | FunCall (_, ins, outs) -> checkLhsRhs outs ins
        | BoolConst _ | IntConst _ | BitsConst _ | NatConst _ | FloatConst _ | ResetConst -> Ok ()
        | StructConst fields ->
            applyToList (snd >> checkAbsenceOfSyncExpr) fields
        | ArrayConst fields ->
            applyToList (snd >> checkAbsenceOfSyncExpr) fields
        | Convert (e, _, _) 
        | Neg e 
        | Bnot e -> checkAbsenceOfSyncExpr e
        | Conj (e1, e2)
        | Disj (e1, e2)
        | Les (e1, e2)
        | Leq (e1, e2)
        | Equ (e1, e2)
        | Add (e1, e2)
        | Sub (e1, e2)
        | Mul (e1, e2)
        | Div (e1, e2)
        | Mod (e1, e2)
        | Band (e1, e2)
        | Bor (e1, e2)
        | Bxor (e1, e2)
        | Shl (e1, e2)
        | Shr (e1, e2)
        | Sshr (e1, e2)
        | Rotl (e1, e2)
        | Rotr (e1, e2) ->
            [e1; e2] |> applyToList checkAbsenceOfSyncExpr

    let rec checkAbsenceOfSyncStmt oneStmt =
        match oneStmt with
        // atomic imperative statements are Ok
        | Stmt.VarDecl v ->
            checkAbsenceOfSyncExpr v.initValue
        | Assert (_,cond,_) | Assume (_,cond,_) ->
            checkAbsenceOfSyncExpr cond
        | Assign (_,lhs,rhs) -> checkLhsRhs [lhs] [rhs]
        | Stmt.Print (_,_,exprLst) ->
            applyToList checkAbsenceOfSyncExpr exprLst
        | FunctionCall (_, _, ins, outs) ->
            checkLhsRhs outs ins
        | Return (_,exprOpt) ->
            exprOpt 
            |> Option.map checkAbsenceOfSyncExpr 
            |> Option.defaultValue (Ok ())
        | Stmt.ExternalVarDecl v ->
            Error [ExternalsInFunction v.pos]
        // synchronous statements
        | Await (p,_) | ActivityCall (p,_,_,_,_) | Preempt (p,_,_,_,_) | Cobegin (p,_)
        | RepeatUntil (p,_,_, true) -> // we do not care about prev in args when the stmt is sychronous
            Error [SynchronousStatementInFunction p]
        // imperative statements containing statements
        | StmtSequence stmts -> checkAbsenceOfSyncStmts stmts
        | WhileRepeat (_, cond, stmts) 
        | RepeatUntil (_, stmts, cond, false) -> 
            [ checkAbsenceOfSyncExpr cond
              checkAbsenceOfSyncStmts stmts ]
            |> applyToList id
        | ITE (_, cond, ifBranch, elseBranch) ->
            [ checkAbsenceOfSyncExpr cond
              ifBranch @ elseBranch |> checkAbsenceOfSyncStmts ]
            |> applyToList id

    applyToList checkAbsenceOfSyncStmt stmts


/// An activity must have some synchronous delay statement on every possible 
/// execution path through its body.
/// This can be an await or a run statement.
// This is partially double work with causality analysis, 
// here and there we will find instantaneous loops.
// Here we throw an error if that is the only statement in the activity.
// In causality analysis we throw an error any way.
let private checkStmtsWillPause p name stmts =
    /// Given a statement (which may actually span a tree of statements),
    /// check that on every path we must hit a delaying statement.
    let rec areAllPathsWithDelay oneStmt =
        match oneStmt with
        // immediate statements
        | Stmt.VarDecl _ | Assign _ | Assert _ | Assume _ | Stmt.Print _
        | Stmt.ExternalVarDecl _ | FunctionCall _ | Return _ 
        | WhileRepeat _ -> false // a while could be skipped over (we do not try to evaluate the condition)
        // delay statements
        | Await _ | ActivityCall _ -> true
        // statements containing statements
        | RepeatUntil (_, stmts, _, _)
        | Preempt (_,_,_,_,stmts) ->
            areAllPathsWithDelay (StmtSequence stmts)
        | ITE (_, _, ifBranch, elseBranch) ->
            areAllPathsWithDelay (StmtSequence ifBranch)
            && areAllPathsWithDelay (StmtSequence elseBranch)
        | StmtSequence stmts -> 
            List.exists areAllPathsWithDelay stmts // false for empty list
        | Cobegin (_,blocks) ->
            // we could allow instantaneous blocks whenever there is at least one
            // strong block which delays - but this is complex to check and explain 
            // to the user and seems fragile from a programmer's point of view
            blocks
            |> List.unzip
            |> snd
            |> List.map (StmtSequence >> areAllPathsWithDelay)
            |> List.forall id // cobegin delays if every block delays

    areAllPathsWithDelay (StmtSequence stmts)
    |> function
        | true -> Ok ()
        | false -> Error [ActivityHasInstantaneousPath(p, name)]


let private determineExternals lut bodyRes =
    let rec searchExternalVarDecl oneStmt =
        let searchUnzipAndCollect xs = 
            let (ins, outs) = xs |> List.map searchExternalVarDecl |> List.unzip
            ins |> List.concat |> List.distinct, 
            outs |> List.concat |> List.distinct
        match oneStmt with
        | Stmt.ExternalVarDecl v when v.mutability.Equals Mutability.Variable -> [],[v] // add v to this scope for code generation
        | Stmt.ExternalVarDecl v when v.mutability.Equals Mutability.Immutable -> [v],[]
        //atomic statements which are not a mutable external variable
        | Stmt.VarDecl _ | Assign _ | Assert _ | Assume _ | Stmt.Print _
        | Stmt.ExternalVarDecl _ | FunctionCall _ | Return _
        | Await _ | ActivityCall _ -> [],[]
        // note that since external variables cannot appear inside functions, we ignore function calls
        // on the statement level AND all expressions that could call functions
        // statements containing statements
        | RepeatUntil (_, stmts, _, _)
        | Preempt (_,_,_,_,stmts)
        | WhileRepeat (_, _, stmts)
        | StmtSequence stmts ->
            stmts |> searchUnzipAndCollect
        | ITE (_, _, ifBranch, elseBranch) ->
            ifBranch @ elseBranch 
            |> searchUnzipAndCollect
        | Cobegin (_, blocks) ->
            blocks
            |> List.unzip
            |> snd
            |> List.concat
            |> searchUnzipAndCollect

    match bodyRes with
    | Error _ -> [],[]
    | Ok body -> searchExternalVarDecl (StmtSequence body)


let private determineCalledSingletons lut bodyRes =
    let rec processFunCall name inputs outputs =
        match lut.nameToDecl.[name] with
        | ProcedureImpl spd -> spd.Singletons
        | ProcedurePrototype fp -> fp.singletons
        | Declarable.VarDecl _ 
        | Declarable.ExternalVarDecl _ 
        | Declarable.ParamDecl _ -> failwith "Expected to check a function declaration for singletons."
        @ List.collect singletonCalls inputs
        @ checkLhs outputs
    and checkLhs lhss =
        let checkLhs out =
            match out.lhs with
            | Wildcard -> []
            | ReturnVar -> []
            | LhsCur tml
            | LhsNext tml ->
                tml.FindAllIndexExpr
                |> List.collect singletonCalls
        lhss |> List.collect checkLhs
    and checkOptReceiver optRcv = 
        match optRcv with
        | Some (UsedLoc lhs) -> 
            checkLhs [lhs]
        | Some (FreshLoc _)
        | Some (ReturnLoc _)
        | None -> 
            []
    and singletonCalls expr =
        let recurFields fields =
            fields
            |> List.collect (snd >> singletonCalls)
        match expr.rhs with
        // locations
        | RhsCur tml
        | Prev tml -> tml.FindAllIndexExpr |> List.collect singletonCalls
        // constants and literals
        | BoolConst _ | IntConst _ | BitsConst _ | NatConst _ | FloatConst _ | ResetConst _ -> []
        | StructConst fields -> recurFields fields
        | ArrayConst elems -> recurFields elems
        // call, has no side-effect IFF it does not write any outputs
        // this assumption is only valid when there are not global variables (as is the case in Blech)
        // and no external C variables are written (TODO!)
        | FunCall (name, inputs, outputs) ->
            processFunCall name inputs outputs
        // unary
        | Convert (e, _, _)
        | Neg e 
        | Bnot e -> 
            singletonCalls e
        // logical
        | Conj (x, y) | Disj (x, y) 
        // bitwise
        | Band (x, y) | Bor(x, y) | Bxor (x, y)
        | Shl (x, y) | Shr (x, y) | Sshr (x, y) | Rotl (x, y) | Rotr (x, y) 
        // relational
        | Les (x, y) | Leq (x, y) | Equ (x, y)
        // arithmetic
        | Add (x, y) | Sub (x, y) | Mul (x, y) | Div (x, y) | Mod (x, y) -> 
            singletonCalls x @ singletonCalls y

    let rec searchSingletons oneStmt =
        match oneStmt with
        // aggregate singletons from subprograms
        | ActivityCall (_, name, receiverOpt, inputs, outputs) ->
            let recSingletons = 
                match lut.nameToDecl.[name] with
                | ProcedureImpl spd -> spd.Singletons
                | ProcedurePrototype p -> p.singletons
                | _ -> failwith "Activity declaration expected, found something else" // cannot happen anyway
            let resInputs = List.collect singletonCalls inputs
            let resReceiver = checkOptReceiver receiverOpt 
            let resOutputs = outputs |> checkLhs
            recSingletons @ resReceiver @ resInputs @ resOutputs
        | FunctionCall (_, name, inputs, outputs) ->
            processFunCall name inputs outputs
        //atomic statements 
        | Stmt.VarDecl v -> singletonCalls v.initValue
        | Assign (_,lhs,rhs) ->
            List.collect singletonCalls [rhs]
            @ checkLhs [lhs]
        | Assert (_,rhs,_) 
        | Assume (_,rhs,_)
        | Await (_,rhs) -> singletonCalls rhs
        | Stmt.Print (_, _, rhss) -> List.collect singletonCalls rhss
        | Stmt.ExternalVarDecl _ -> []
        | Return (_,rhsOpt) -> 
            rhsOpt
            |> Option.map singletonCalls 
            |> Option.defaultValue []
        // statements containing statements
        | RepeatUntil (_, stmts, rhs, _)
        | Preempt (_,_,rhs,_,stmts)
        | WhileRepeat (_, rhs, stmts) ->
            singletonCalls rhs
            @ List.collect searchSingletons stmts
        | StmtSequence stmts ->
            List.collect searchSingletons stmts
        | ITE (_, rhs, ifBranch, elseBranch) ->
            singletonCalls rhs
            @ List.collect searchSingletons (ifBranch @ elseBranch)
        | Cobegin (_, blocks) ->
            blocks
            |> List.unzip
            |> snd
            |> List.concat
            |> List.collect searchSingletons

    match bodyRes with
    | Error _ -> []
    | Ok body ->
        searchSingletons (StmtSequence body) 
        |> List.distinct // filter out multiple calls to the same function/activity
        
//=============================================================================
// Short-hand stuff
//=============================================================================

/// Forms a single conjunction from given list of guards
let private mkGuard guards = 
    match guards with
    | [] -> Error[EmptyGuardList]
    | [g] -> Ok g
    | g :: gs ->
        let folder expr partResult =
            { rhs = unsafeConj expr partResult; 
              typ = ValueTypes BoolType; 
              range = Range.unionRanges expr.Range partResult.Range }
        List.foldBack folder gs g |> Ok 


/// Temporary shortcut.
/// Rewrites a while loop into a repeat loop that is surrounded by an if.
/// Eventually get rid of this and make while an instantaneous language construct
/// that is distinguished from (possibly multi-step) repeat loops.
let private makeWhile pos prog cond =
    let loop = Stmt.RepeatUntil (pos, prog, {cond with rhs = unsafeNeg cond}, false)
    ITE (pos, cond, [loop], []) |> Ok


// Dummies for unsupported language construct
let private unsupported1 str r = Error [UnsupportedFeature (r, str)]
let private unsupported2 str r _ = Error [UnsupportedFeature (r, str)]
let private unsupported3 str r _ _ = Error [UnsupportedFeature (r, str)]
let private unsupported4 str r _ _ _ = Error [UnsupportedFeature (r, str)]
let private unsupported5 str r _ _ _ _ = Error [UnsupportedFeature (r, str)]
let private unsupported6 str r _ _ _ _ _ = Error [UnsupportedFeature (r, str)]
let private unsupported9 str r _ _ _ _ _ _ _ _ = Error [UnsupportedFeature (r, str)]

   
//=============================================================================
// Creating variable or subprogram declarations
//=============================================================================

/// Check a type annotation
let rec private fDataType = checkDataType

/// Create a variable declaration. It may be local to a subprogram or global.
/// It may be mutable or immutable (when local).
let private fVarDecl lut pos (name: Name) permission dtyOpt initValOpt vDeclAnno =
    let mutability =
        match permission with 
        | AST.ReadOnly (ro, _) ->
            match ro with
            | AST.Let -> Mutability.Immutable
            | AST.Const -> Mutability.CompileTimeConstant
            | AST.Param -> Mutability.StaticParameter
        | AST.ReadWrite _ -> Mutability.Variable
    
    let checkMutabilityCompliance (checkedDty, checkedInitExpr) =
        if mutability.Equals Mutability.CompileTimeConstant then
            // get *value* of checkedInitExpr here
            evalConst lut checkedInitExpr
            |> Result.map (fun constExpr -> checkedDty, constExpr)
        elif mutability.Equals Mutability.StaticParameter then
            // Ensure that init expr of params has only static data
            if isStaticExpr lut checkedInitExpr then
                Ok (checkedDty, tryEvalConst lut checkedInitExpr)
            else
                Error [ParameterMustHaveStaticInit(name, checkedInitExpr)]
        else 
            // try, if rhs is constant by any chance, if not that's fine too
            Ok (checkedDty, tryEvalConst lut checkedInitExpr)
        

    let createVarDecl ((qualifiedName, (dty, value)), anno) =
        let v = {
            pos = pos
            BlechTypes.VarDecl.name = qualifiedName
            datatype = dty
            mutability = mutability
            initValue = value
            annotation = anno
            allReferences = HashSet()
        }    
        do addDeclToLut lut qualifiedName (Declarable.VarDecl v)
        v

    let dtyAndInit = 
        alignOptionalTypeAndValue pos name.id dtyOpt initValOpt
        |> Result.bind checkMutabilityCompliance
        
    Ok (lut.ncEnv.nameToQname name)
    |> combine <| dtyAndInit
    |> combine <| vDeclAnno
    |> Result.map createVarDecl


let private fExternalVarDecl lut pos (name: Name) permission dtyOpt initValOpt vDeclAnno =
    let dtyGiven =
        // datatype must be given
        match dtyOpt with
        | None -> failwith "It should be syntactically impossible to declare an external variable without an explicit datatype."
        | Some dty -> dty
        
    let checkNoInit =        
        // no init value is allowed
        match initValOpt with
        | Some _ -> failwith "It should be syntactically impossible to declare an external variable with initialisation."
        | None -> Ok ()
            
    let checkMutability =
        match permission with 
        | AST.ReadOnly (ro, _) ->
            match ro with
            | AST.Const -> Ok Mutability.CompileTimeConstant
            | AST.Let -> Ok Mutability.Immutable
            | AST.Param -> Ok Mutability.StaticParameter
        | AST.ReadWrite _ -> Ok Mutability.Variable

    let createExternalVarDecl ((((qualifiedName, dty),mutability),anno),_)=
        let v = {
            pos = pos
            BlechTypes.ExternalVarDecl.name = qualifiedName
            datatype = dty
            mutability = mutability
            annotation = anno
            allReferences = HashSet()
        }    
        do addDeclToLut lut qualifiedName (Declarable.ExternalVarDecl v)
        v

    Ok (lut.ncEnv.nameToQname name)
    |> combine <| dtyGiven
    |> combine <| checkMutability
    |> combine <| vDeclAnno
    |> combine <| checkNoInit
    |> Result.map createExternalVarDecl

let private recVarDecl lut (v: AST.VarDecl) =
    assert (not v.isExtern)
    fVarDecl lut v.range v.name v.permission
    <| Option.map (fDataType lut) v.datatype
    <| Option.map (checkExpr lut) v.initialiser
    <| Annotation.checkVarDecl lut v 

let private chkExternalVarDecl lut (v: AST.VarDecl) =
    assert v.isExtern
    fExternalVarDecl lut v.range v.name v.permission 
    <| Option.map (fDataType lut) v.datatype
    <| Option.map (checkExpr lut) v.initialiser
    <| Annotation.checkVarDecl lut v 


let private fParamDecl lut pos name mutableFlag dtyRes = 
    let createArgDecl (qualifiedName, dty) =
        let a = {
            pos = pos
            BlechTypes.ParamDecl.name = qualifiedName
            datatype = dty
            isMutable = mutableFlag
            allReferences = HashSet()
        }
        do addDeclToLut lut qualifiedName (Declarable.ParamDecl a)
        a

    (Ok (lut.ncEnv.nameToQname name),
        dtyRes)
    ||> combine
    |> Result.map createArgDecl


/// Type check a function prototype
let private fFunPrototype lut kind pos name isSingleton inputs outputs retType annotation =
    let createFunPrototype ((((qname, ins), outs), ret), annotation) = 
        let funPrototype =
            {
                ProcedurePrototype.pos = pos
                kind = kind
                singletons = if isSingleton then [qname] else []
                name = qname
                inputs = ins
                outputs = outs
                returns = ret
                annotation = annotation
                allReferences = HashSet()
            }
        do addDeclToLut lut qname (Declarable.ProcedurePrototype funPrototype)
        funPrototype

    // check that it is a first class type
    let checkReturn rets  =
        match rets with
        | None -> Void |> Ok
        | Some ret ->
            ret |> Result.bind (
                function
                | ValueTypes f -> f |> Ok 
                | _ -> Error [MustReturnFirstClassType (pos, name.id)]
                )

    Ok (lut.ncEnv.nameToQname name)
    |> combine <| contract inputs
    |> combine <| contract outputs
    |> combine <| checkReturn retType
    |> combine <| annotation
    |> Result.map createFunPrototype


/// Type check a sub program
let private fSubProgram lut pos isFunction name isSingleton inputs outputs retType body annotation =
    let createSubProgram (globalInputs, localGlobalOutputs, singletons) ((((qname, prototype),_), stmts), annotation) = 
        let prototype = {prototype with singletons = prototype.singletons @ singletons |> List.distinct}
        let funact =
            {
                ProcedureImpl.prototype = prototype
                pos = pos
                globalInputs = globalInputs
                globalOutputsInScope = localGlobalOutputs
                body = stmts
                annotation = annotation
                allReferences = HashSet()
            }
        do addDeclToLut lut qname (Declarable.ProcedureImpl funact)
        funact
    // check that there is only one return value and it is a first class type
    let checkReturn rets bodyContractionRes =
        match rets with
        | None -> Void |> Ok
        | Some ret ->
            ret |> Result.bind (
                function
                | ValueTypes f -> f |> Ok 
                | _ -> Error [MustReturnFirstClassType (pos, name.id)]
                )
        |> Result.bind(fun typedRet ->
            match bodyContractionRes with
            | Ok stmts -> checkStmtsMatchReturn pos (Stmt.StmtSequence stmts) typedRet
            | _ -> typedRet |> Ok
            )
    let contractedBody =
        let cb = contract body 
        if isFunction then
            cb
            |> Result.bind checkAbsenceOfSyncStmts // also excludes external variables
            |> Result.bind (fun _ -> cb) // if no synchronous statements were found, return the contracted body
        else
            cb
            |> Result.bind (checkStmtsWillPause pos name)
            |> Result.bind (fun _ -> cb) // if there is no instantaneous path, return the contracted body
    
    let externalInputs, externalOutputs = determineExternals lut contractedBody
    let singletons = 
        if isSingleton || not (List.isEmpty externalOutputs) then [lut.ncEnv.nameToQname name]
        else []
        @ determineCalledSingletons lut contractedBody

    let kind = if isFunction then LocalFunction else Activity
    let checkedPrototype = fFunPrototype lut kind pos name isSingleton inputs outputs retType (Ok Attribute.FunctionPrototype.Empty)

    Ok (lut.ncEnv.nameToQname name)
    |> combine <| checkedPrototype
    |> combine <| checkReturn retType contractedBody
    |> combine <| contractedBody
    |> combine <| annotation
    |> Result.map (createSubProgram (externalInputs, externalOutputs, singletons))


//=============================================================================
// Creating user defined type declarations (structs, enums, ...)
//=============================================================================

let private fStructTypeDecl lut (std: AST.StructTypeDecl) =
    let checkValueFields fields =
        fields
        // ensure the fields are all variable declarations
        |> List.choose (function | AST.Member.Var v -> Some v | _ -> None) 
        // typify struct fields
        |> List.map (recVarDecl lut) // type check field declarations as variable declarations
        // make sure they are of value type
        |> List.map (Result.bind (fun v -> if v.datatype.IsValueType then Ok v else Error[ValueStructContainsRef (std.name, v)]))
        |> contract

    let checkAllFields fields =
        fields
        // ensure the fields are all variable declarations
        |> List.choose (function | AST.Member.Var v -> Some v | _ -> None) 
        // typify struct fields
        |> List.map (recVarDecl lut) // type check field declarations as variable declarations
        |> contract // here we do not care, if the datatype is value or reference type
        
        // note, that QNames for the fields are added when checking the individual vardecls

    // decide if it is a ref type
    // and then check types of fields
    let qname = lut.ncEnv.nameToQname std.name
    let newType =
        if std.isReference then
            // create reference type
            Ok qname
            |> combine <| checkAllFields std.fields
            |> Result.map (
                fun (q, f) -> (std.name.Range, q, f)
                >> ReferenceTypes.StructType >> ReferenceTypes )
        else
            // create value type
            Ok qname
            |> combine <| checkValueFields std.fields
            |> Result.map (
                fun (q, f) -> (q, f)
                >> ValueTypes.StructType >> ValueTypes )
    // add type declaration to lookup table
    match newType with
    | Ok typ -> do addTypeToLut lut qname std.name.Range typ
    | _ -> ()
    newType

        
let private fOpaqueTypeDecl pos = unsupported3 "new type declarations" pos //TODO
let private fTypeAliasDecl pos = unsupported4 "alias declarations" pos //TODO
let private fEnumTypeDecl (etd: AST.EnumTypeDecl) = unsupported1 "enum declarations" etd.range //TODO 
let private fUnitDecl pos = unsupported4 "unit declarations" pos //TODO
let private fClockDecl (cld: AST.ClockDecl) = unsupported1 "clock declarations" cld.range //TODO


//=============================================================================
// Receivers and Conditions
//=============================================================================

let private fFreshLocation lut pos (name: Name) permission (rhsTyp: Types) dtyOpt vDeclAnno =
    let mutability =
        match permission with 
        | AST.ReadOnly (ro, _) ->
            match ro with
            | AST.Let -> Mutability.Immutable
            | _ -> failwith "Location must not be const or param"
        | AST.ReadWrite _ -> Mutability.Variable
    
    let createVarDecl ((qualifiedName, (dty, initVal)), anno) =
        let v = {
            pos = pos
            BlechTypes.VarDecl.name = qualifiedName
            datatype = dty
            mutability = mutability
            initValue = 
                match dty with
                | ValueTypes (ValueTypes.OpaqueSimple _) ->
                    {rhs = NatConst Constants.Nat.Zero8; typ = ValueTypes (NatType Nat8); range = pos} // 0 for simple types
                | ValueTypes (ValueTypes.OpaqueComplex _) ->
                    {rhs = ArrayConst [Constants.SizeOne, {rhs = NatConst Constants.Nat.Zero8; typ = ValueTypes (NatType Nat8); range = pos}]; typ = ValueTypes (ValueTypes.ArrayType(Constants.SizeOne, ValueTypes.NatType Nat8)); range = pos} // {0} for complex types
                | _ ->
                    initVal
            annotation = anno
            allReferences = HashSet()
        }    
        do addDeclToLut lut qualifiedName (Declarable.VarDecl v)
        v

    let dtyAndInit = 
        let dtyRes = 
            match dtyOpt with
            | None -> Ok rhsTyp  // if no datatype is given take the activity return type as the location type
            | Some lhsTypRes -> lhsTypRes    
        dtyRes
        |> Result.map (fun dty ->
            match dty with
            | ValueTypes (ValueTypes.OpaqueSimple _) ->
                Ok {rhs = NatConst Constants.Nat.Zero8; typ = ValueTypes (NatType Nat8); range = pos} // 0 for simple types
            | ValueTypes (ValueTypes.OpaqueComplex _) ->
                Ok {rhs = ArrayConst [Constants.SizeOne, {rhs = NatConst Constants.Nat.Zero8; typ = ValueTypes (NatType Nat8); range = pos}]; typ = ValueTypes (ValueTypes.ArrayType(Constants.SizeOne, ValueTypes.NatType Nat8)); range = pos} // {0} for complex types
            | _ ->
                getInitValueWithoutZeros Range.range0 "" dty
            )
        |> Result.bind (combine dtyRes)
        

    Ok (lut.ncEnv.nameToQname name)
    |> combine <| dtyAndInit
    |> combine <| vDeclAnno
    |> Result.map createVarDecl

let private checkFreshLocation lut (v: AST.VarDecl) (rhsTyp: Types) =
    assert (Option.isNone v.initialiser)
    fFreshLocation lut v.range v.name v.permission rhsTyp
    <| Option.map (fDataType lut) v.datatype
    <| Annotation.checkVarDecl lut v 

let private checkAssignReceiver pos lut (rcvOpt: AST.Receiver option) decl = 

    let checkReturnType (storage: Receiver option) declName declReturns =
        match storage with
        | None ->
            match declReturns with
            | Void -> Ok None
            | _ -> Error [ActCallMustExplicitlyIgnoreResult (pos, declName.basicId)]
        | Some receiver ->
            match receiver.Typ with 
            | Any -> // wildcard
                Ok None
            | ValueTypes _ ->
                Ok storage 
            | _ -> Error [ ValueMustBeOfValueType (receiver) ]  // TOOD: This will change with references, fjg 30.06.20
        |> Result.bind (
            function
            | None -> Ok None
            | Some (ReturnLoc {typ = t}) ->
                if isLeftSupertypeOfRight t (ValueTypes declReturns) then 
                    Ok storage 
                else 
                    Error [ReturnTypeMismatch(pos, t, ValueTypes declReturns)]                
            | Some (FreshLoc vdecl) ->
                let typ = vdecl.datatype
                if isLeftSupertypeOfRight typ (ValueTypes declReturns) then 
                    Ok storage 
                else 
                    Error [ReturnTypeMismatch(pos, typ, ValueTypes declReturns)]
            | Some (UsedLoc tlhs) ->
                let typ = tlhs.typ
                if isLhsMutable lut tlhs.lhs then
                    if isLeftSupertypeOfRight typ (ValueTypes declReturns) then 
                        Ok storage 
                    else 
                        Error [ReturnTypeMismatch(pos, typ, ValueTypes declReturns)]
                else Error [AssignmentToImmutable (pos, tlhs.ToString())]
            )
    
    let checkNeedForReceiver (rcvOpt: AST.Receiver option) decl =
        match rcvOpt with
        | Some location ->
            match decl.returns with
            | Void ->
                Error [ReceiverForVoidReturn (location.Range, decl)]
            | _ ->
                Ok (Some location)
        | None ->
            match decl.returns with
            | Void -> 
                Ok None                
            | _ ->
                Error [MissingReceiver (pos, decl)]
                
    let checkLocation rcv =
        match rcv with
        | Some (AST.Location lhs) ->
            checkAssignLExpr lut lhs
            |> Result.bind (fun tlhs -> Ok (Some (UsedLoc tlhs)))
        | Some (AST.FreshLocation vdecl) ->
            checkFreshLocation lut vdecl (ValueTypes decl.returns)   // TODO: Currently the return value must be a value types, this might change
            |> Result.bind (fun tvdecl -> Ok (Some (FreshLoc tvdecl)))
        | Some (AST.ReturnLocation rng) ->
            Ok (Some (ReturnLoc { lhs = ReturnVar; typ = ValueTypes decl.returns; range = rng })) 
        | None ->
            Ok None
    
    checkNeedForReceiver rcvOpt decl
    |> Result.bind checkLocation
    |> Result.bind (fun receiver -> checkReturnType receiver decl.name decl.returns)


/// Type check activity calls.
/// An activity may return a value that is stored in resStorage upon termination.
/// This is different to a function call
let private fActCall lut pos (rcv: AST.Receiver option) (ap: AST.Code) (inputs: Result<_,_> list) outputs =
    let checkIsActivity (decl: ProcedurePrototype) =
        if decl.IsActivity then Ok()
        else Error [RunAFun(pos, decl)]
    
    let createCall name (((_, ins), outs), retvar) =
        ActivityCall (pos, name, retvar, ins, outs)
    
    match ap with
    | AST.Procedure dname ->
        ensureCurrent dname
        |> Result.map lut.ncEnv.dpathToQname
        |> Result.bind (getSubProgDeclAsPrototype lut pos)
        |> Result.bind (fun decl ->
            checkIsActivity decl
            |> combine <| checkInputs pos inputs decl.name decl.inputs
            |> combine <| checkOutputs lut pos outputs decl.name decl.outputs
            |> combine <| checkAssignReceiver pos lut rcv decl
            |> Result.map (createCall decl.name)
            )




//=============================================================================
// Define all actions for AST transformation and do the type checking
//=============================================================================

let private fAssign lut pos lhs rhs =
    let createAssign myleft (myright: TypedRhs) =
        amendRhsExpr myleft.typ myright
        |> Result.map (fun amendedRight -> Assign (pos, myleft, amendedRight))
    
    lhs
    |> combine <| rhs
    |> Result.bind (fun (l, r) -> 
        if isLhsMutable lut l.lhs then
            createAssign l r
        else Error [AssignmentToImmutable (pos, l.ToString())]
        )


let private generateVC isAssertion pos conditions msgOpt =
    let createAssume guards =
        let guard = // conjunction of given guards
            match guards with
            | [] -> failwith "Making an empty VC should be impossible!"
            | [g] -> g
            | g::gg ->
                List.foldBack (fun e acc -> {rhs = Conj(e, acc); typ = ValueTypes BoolType; range = pos}) gg g
        let msg = // if no message was specified, simply take the string representation of the condition that needs to be verified here
            match msgOpt with 
            | Some (AST.Expr.Const (AST.Literal.String (txt, _))) -> txt 
            | _ -> guard.ToString()
        if isAssertion then
            Assert(pos, guard, msg)
        else
            Assume(pos, guard, msg)
    
    conditions
    |> contract
    |> Result.map (createAssume)


let private fAssert = generateVC true
let private fAssume = generateVC false
       
       
let private fAwait pos conditions =
    contract conditions // conditions are ensured to be without side-effects
    |> Result.bind mkGuard
    |> Result.map (fun gg -> Await (pos, gg))
    

let private fITE pos conditions ifStmts elseStmts _ =
    let ifBranch = contract ifStmts
    let elseBranch = contract elseStmts
        
    contract conditions
    |> Result.bind mkGuard 
    |> combine <| combine ifBranch elseBranch
    |> Result.map (fun (g,(i,e)) -> ITE(pos, g, i, e))


let private fCobegin pos blocks =
    blocks
    |> List.map (fun (str,body) -> contract body |> Result.map (fun stmts -> str, stmts))
    |> contract
    |> Result.map (fun x -> Cobegin (pos, x))
    

let private fWhile pos conditions stmts =
    contract conditions
    |> Result.bind mkGuard
    |> combine <| contract stmts
    |> Result.bind (fun (g, s) -> makeWhile pos s g)


let private fRepeat pos stmts conditions endlessFlag =
    let createRepeatUntil (guard, body) =
        RepeatUntil (pos, body, guard, endlessFlag)
    let guard =
        if endlessFlag then
            {rhs = BoolConst false; typ = ValueTypes BoolType; range = pos} |> Ok
        else
            contract conditions
            |> Result.bind mkGuard
    contract stmts
    |> combine guard
    |> Result.map createRepeatUntil


let private fNumericFor = unsupported6 "for-loops" //TODO

let private fIteratorFor = unsupported5 "for-iterators" //TODO

let private fPreempt range preemption moment conds body =
    let createPreemption (c, b) = Preempt (range, preemption, c, moment, b)
        
    // we could introduce a warning if body has no delay (preemption useless)
    // checkStmtsWillPause range name body

    match moment with 
    // we do not support OnNext preemptions yet
    | Moment.OnNext -> unsupported1 "Next step preemptions are not yet supported." range 
    | _ -> 
        conds 
        |> contract 
        |> Result.bind mkGuard
        |> combine <| contract body
        |> Result.map createPreemption
        

/// collect errors, if there are none, return Ok of StmtSequence
let private fSubScope _ stmts =
    contract stmts
    |> Result.map StmtSequence


let private fFunCall lut pos fp inputs outputs =
    checkFunCall true lut pos fp inputs outputs
    |> Result.map(fun ((n, i, o), _) -> FunctionCall (pos, n, i, o))


let private fEmit = unsupported3 "event emissions" //TODO


/// Check that type of returned expression fits the declared return type of a subprogram
/// retTypOpt is the declared return type of the subprogram (None corresponds to void)
/// exprOpt is the expression of the return statement (None corresponds to empty return)
let private fReturn retTypOpt pos exprOpt =
    match retTypOpt, exprOpt with
    | None, None -> Return (pos, None) |> Ok
    | Some retTyp, Some expr ->
        combine retTyp expr 
        |> Result.bind (fun (r, e) -> amendRhsExpr r e)
        |> Result.bind (fun (e: TypedRhs) -> match e.typ with | ValueTypes _ -> Ok e | _ -> Error [NonFirstClassReturnStmt pos])
        |> Result.map (fun e -> Return (pos, Some e))
    | None, Some _ -> Error [VoidSubprogCannotReturnValues(pos)]
    | Some tr, None -> tr |> Result.bind (fun t -> Error [VoidReturnStmtMustReturn(pos,t)])

let private fPragma = unsupported1 "pragma inside stmt sequence"

let private fNothing = unsupported1 "the empty statement" Range.range0

//=============================================================================
// Recurse through the AST, calling relevant functions from above
//=============================================================================

// this alias is used to help F#'s type system. Otherwise it is not possible to find Stmt.FunctionCall, for example.
type private ASTStmt = AST.Stmt 

let rec private recStmt lut retTypOpt x = // retTypOpt is required for amending the expression in a "return" statement
    match x with
    | AST.LocalVar vdecl ->
        if vdecl.isExtern then
            chkExternalVarDecl lut vdecl
            |> Result.map (Stmt.ExternalVarDecl)
        else
            recVarDecl lut vdecl
            |> Result.map (Stmt.VarDecl)
    | AST.Assign (range, lhs, rhs) ->
        fAssign lut range
        <| checkAssignLExpr lut lhs
        <| (checkExpr lut rhs |> Result.map(tryEvalConst lut))
    | AST.Assert (range, conds, msg) ->
        fAssert range (List.map (fCondition lut) conds) msg
    | AST.Assume (range, conds, msg) ->
        fAssume range (List.map (fCondition lut) conds) msg
    // pause
    | AST.Await (range, conds) ->
        fAwait range (List.map (fCondition lut) conds)
    // control flow
    | AST.ITE (range, conds, bodyIf, (bodyElse, isElseIf)) ->
        fITE range
        <| List.map (fCondition lut) conds
        <| List.map (recStmt lut retTypOpt) bodyIf
        <| List.map (recStmt lut retTypOpt) bodyElse
        <| isElseIf
    | AST.Cobegin (range, blockList) ->
        let processBlock (strength, stmts) =
            (strength, List.map (recStmt lut retTypOpt) stmts)
        fCobegin range
        <| List.map processBlock blockList
    | AST.WhileRepeat (range, conds, body) ->
        fWhile range
        <| List.map (fCondition lut) conds
        <| List.map (recStmt lut retTypOpt) body
    | AST.RepeatUntil (range, body, conds) ->
        fRepeat range
        <| List.map (recStmt lut retTypOpt) body
        <| List.map (fCondition lut) conds
        <| List.isEmpty conds // endless loop if there are no conditions
    | AST.NumericFor (range, var, init, limit, step, body) ->
        fNumericFor range
        <| recVarDecl lut var
        <| (checkExpr lut init |> Result.map(tryEvalConst lut))
        <| (checkExpr lut limit |> Result.map(tryEvalConst lut))
        <| Option.map (checkExpr lut >> Result.map(tryEvalConst lut)) step
        <| List.map (recStmt lut retTypOpt) body
    | AST.IteratorFor (range, var, iterator, iterable, body) ->
        fIteratorFor range iterator
        <| recVarDecl lut var
        <| (checkExpr lut iterable |> Result.map(tryEvalConst lut))
        <| List.map (recStmt lut retTypOpt) body
    // observation
    | AST.Preempt (range, preemption, conds, moment, body) ->
        fPreempt range preemption moment
        <| List.map (fCondition lut) conds
        <| List.map (recStmt lut retTypOpt) body
    // scoping
    | AST.SubScope (range, body) ->
        fSubScope range <| List.map (recStmt lut retTypOpt) body
    // calling
    | AST.ActivityCall (range, optReceiver, pname, inputOptList, outputOptList) ->
        fActCall lut range optReceiver pname
        //<| Option.map ( checkAssignReceiver lut) optReceiver
        <| List.map (checkExpr lut >> Result.map(tryEvalConst lut)) inputOptList
        <| List.map (checkLExpr lut) outputOptList
    | ASTStmt.FunctionCall (range, pname, inputOptList, outputOptList) ->
        fFunCall lut range pname
        <| List.map (checkExpr lut >> Result.map(tryEvalConst lut)) inputOptList
        <| List.map (checkLExpr lut) outputOptList
    | AST.Emit(range, pname, optExpr) ->
        fEmit range pname optExpr
    | AST.Return (range, optExpr) ->
        fReturn retTypOpt range 
        <| Option.map (checkExpr lut >> Result.map(tryEvalConst lut)) optExpr 
    | ASTStmt.Pragma anno ->
        fPragma anno.Range
    | ASTStmt.Nothing ->
        fNothing


let private recParamDecl lut (a: AST.ParamDecl) =
    fParamDecl lut a.range a.name a.isMutable 
    <| fDataType lut a.datatype


let private recReturnDecl lut (a: AST.ReturnDecl) =
    // currently we do not receive the ref and sharing information,
    // so all we do is forward the type
    fDataType lut a.datatype
    

type private ProcessedMembers =
    {
        funacts: Collections.ResizeArray<Result<ProcedureImpl, TyCheckError list>>
        funPrototypes: Collections.ResizeArray<Result<ProcedurePrototype, TyCheckError list>>
        variables: Collections.ResizeArray<Result<VarDecl, TyCheckError list>>
        externalVariables: Collections.ResizeArray<Result<ExternalVarDecl, TyCheckError list>>
        types: Collections.ResizeArray<Result<Types, TyCheckError list>>
        memberPragmas: ResizeArray<Result<Attribute.MemberPragma, TyCheckError list>>
        mutable entryPoint: Result<ProcedureImpl, TyCheckError list> option
    }
    member this.AddFunAct fa = this.funacts.Add fa
    member this.AddFunPrototype fp = this.funPrototypes.Add fp
    member this.AddVariable v = this.variables.Add v
    member this.AddExternalVariable v = this.externalVariables.Add v
    member this.AddType t = this.types.Add t
    member this.AddMemberPragma mp = this.memberPragmas.Add mp
            
    // TODO: Simplify this, fjg 19.01.19
    member this.UpdateEntryPoint (pack: AST.CompilationUnit) (act: Result<ProcedureImpl, _>) =
        let optEp = 
            match act with
            | Ok subprog ->
                if Option.isSome subprog.annotation.entryPoint then 
                    Some subprog   
                else 
                    None
            | Error _ ->
                None

        this.entryPoint <-  
            match optEp, this.entryPoint with
            | Some ep, None when pack.IsProgram  ->
                Some (Ok ep)   
            | Some ep, Some (Ok epFst) when pack.IsProgram ->
                Some (Error [MultipleEntryPoints (epFst.pos, ep.pos)])
            | Some ep, None when pack.IsModule ->
                Some (Error [IllegalEntryPoint (ep.pos, pack)])
            | Some ep, Some (Error err) when pack.IsModule ->
                Some (Error (err @ [IllegalEntryPoint (ep.pos, pack)]))   
            | _, ep ->
                ep

    member this.GetFunActs = List.ofSeq this.funacts
    member this.GetFunPrototypes = List.ofSeq this.funPrototypes
    member this.GetVariables = List.ofSeq this.variables
    member this.GetExternalVariables = List.ofSeq this.externalVariables
    member this.GetTypes = List.ofSeq this.types
    member this.GetMemberPragmas = List.ofSeq this.memberPragmas
    member this.GetEntryPoint = this.entryPoint
            
    static member Empty () =
        {
            funacts = Collections.ResizeArray()
            funPrototypes = Collections.ResizeArray()
            variables = Collections.ResizeArray()
            externalVariables = Collections.ResizeArray()
            types = Collections.ResizeArray()
            memberPragmas = Collections.ResizeArray()
            entryPoint = None
        }


// this is also an entry point for testing, hence public
let public fPackage lut (pack: AST.CompilationUnit) =
    let pos = pack.Range
    //let spec = pack.spec

    let rec processMembers (typedMembers: ProcessedMembers) mems =
        match mems with
        | [] -> 
            typedMembers.GetFunActs,
            typedMembers.GetFunPrototypes,
            typedMembers.GetVariables,
            typedMembers.GetExternalVariables,
            typedMembers.GetTypes,
            typedMembers.GetMemberPragmas,
            typedMembers.GetEntryPoint
        | m::ms ->
            match m with
            | AST.Member.Nothing ->
                () // ignore these members
            | AST.Member.Pragma p ->
                do typedMembers.AddMemberPragma (Annotation.checkMemberPragma lut p)
            | AST.Member.EnumType e -> 
                do typedMembers.AddType (fEnumTypeDecl e)
            | AST.Member.StructType s -> 
                do typedMembers.AddType (fStructTypeDecl lut s)
            | AST.Member.OpaqueType ot ->
                let t =
                    fOpaqueTypeDecl ot.range ot.name
                    <| Annotation.checkOtherDecl ot.annotations
                do typedMembers.AddType t
            | AST.Member.TypeAlias t ->
                let t =
                    fTypeAliasDecl t.range t.name
                    <| fDataType lut t.aliasfor
                    <| Annotation.checkOtherDecl t.annotations
                do typedMembers.AddType t
            | AST.Member.Unit _ ->
                //let _ =
                //    fUnitDecl u.range u.name
                //    <| Option.map fUnitExpr u.definition
                //    <| List.map fAnnotation u.annotations
                () // ignore this member
            | AST.Member.Clock _ -> 
                //let _ = fClockDecl c
                () // ignore this member
            | AST.Member.Var v -> 
                if v.isExtern then
                    chkExternalVarDecl lut v
                    |> typedMembers.AddExternalVariable
                else
                    recVarDecl lut v
                    |> typedMembers.AddVariable
            | AST.Member.Subprogram a ->
                let retTypOpt = Option.map (recReturnDecl lut) a.result
                let funact = 
                    fSubProgram lut a.range a.isFunction a.name a.isSingleton
                    <| List.map (recParamDecl lut) a.inputs
                    <| List.map (recParamDecl lut) a.outputs
                    <| retTypOpt
                    <| List.map (recStmt lut retTypOpt) a.body
                    <| Annotation.checkSubProgram a
                do typedMembers.AddFunAct funact
                do typedMembers.UpdateEntryPoint pack funact
            | AST.Member.Prototype f ->
                let kind = 
                    if f.isOpaque then
                        ProcedureKind.OpaqueProcedure
                    elif f.isExtern && f.isFunction then
                        ProcedureKind.ExternFunction
                    elif not f.isExtern && f.isFunction then
                        ProcedureKind.LocalFunction
                    elif not f.isExtern && not f.isFunction then
                        ProcedureKind.Activity
                    else
                        failwith "Inconsistent prototype AST generated by parser"
                let funPrototype =
                    fFunPrototype lut kind f.range f.name f.isSingleton
                    <| List.map (recParamDecl lut) f.inputs
                    <| List.map (recParamDecl lut) f.outputs
                    <| Option.map (recReturnDecl lut) f.result
                    <| Annotation.checkFunctionPrototype lut f
                do typedMembers.AddFunPrototype funPrototype
            processMembers typedMembers ms
        
    let createPackage (((((((modName, funPrototypes), funacts), variables), externalVariables), types), memberPragmas), entryPoint) =
    
        //assert (List.length types = lut.userTypes.Count) // TODO: this assertion is wrong if we have imported types from other modules, fg 01.10.20
        {
            BlechModule.name = modName
            types = types
            funPrototypes = funPrototypes
            funacts = funacts
            variables = variables
            externalVariables = externalVariables
            memberPragmas = memberPragmas
            entryPoint = entryPoint
        }
    
    let funacts, funPrototypes, variables, externalVariables, types, memberPragmas, entryPoint = 
        let typedMembers = ProcessedMembers.Empty ()
        processMembers typedMembers pack.members
    
    let moduleName = pack.moduleName

    let typedPack = 
        Ok moduleName
        |> combine <| contract funPrototypes
        |> combine <| contract funacts
        |> combine <| contract variables
        |> combine <| contract externalVariables
        |> combine <| contract types
        |> combine <| contract memberPragmas
        |> combine <| ofOption entryPoint
        |> Result.map createPackage
    
    let checkEntryPoint (blechModule: BlechModule) =
        if pack.IsProgram && Option.isNone blechModule.entryPoint then
            Error [MissingEntryPoint pos]
        else
            Ok blechModule
    
    Result.bind checkEntryPoint typedPack


/// Performs type checking starting with an untyped package and a namecheck loopup table.
/// Returns a TypeCheck context and a BlechModule.
let typeCheck (cliContext: Arguments.BlechCOptions) logger otherLuts (pack: AST.CompilationUnit, ncEnv: SymbolTable.Environment) =
    let lut = TypeCheckContext.Init cliContext ncEnv
    otherLuts
    |> List.iter (fun otherLut ->
        // TODO: do we filter here for visibility? opaque procedures and types? fg 22.12.2020
        for pair in otherLut.nameToDecl do addDeclToLut lut pair.Key pair.Value
        for pair in otherLut.userTypes do addTypeToLut lut pair.Key (fst pair.Value) (snd pair.Value)
        for pragma in otherLut.memberPragmas do addPragmaToLut lut pragma
        )
    fPackage lut pack
    |> function
        | Ok p -> 
            Blech.Common.Logging.log6 "Main" ("typed syntax tree built\n" + p.ToString())
            Ok (lut, p)
        | Error errs -> Error (Diagnostics.wrapErrsInLogger logger Diagnostics.Phase.Typing errs)
        