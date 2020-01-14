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
    // atomic statements, except "return"
    | Stmt.VarDecl _ | Assign _ | Assert _ | Assume _ | Stmt.Print _ | Await _ 
    | Stmt.ExternalVarDecl _ | ActivityCall _ | FunctionCall _ -> 
        Ok NoReturn
    // the "return" statement
    | Return (pos, exprOpt) ->
        match exprOpt with 
        | Some expr ->
            match expr.typ with
            | Types.ValueTypes t -> Must t |> Ok
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
                    if isLeftSupertypeOfRight (Types.ValueTypes s) (Types.ValueTypes e) then
                        prev
                    elif isLeftSupertypeOfRight (Types.ValueTypes e) (Types.ValueTypes s) then
                        Ok succ
                    else
                        Error [IncomparableReturnTypes(Range.range0, s, e)]
                | May s, Must e ->
                    if isLeftSupertypeOfRight (Types.ValueTypes s) (Types.ValueTypes e) then
                        Must s |> Ok
                    elif isLeftSupertypeOfRight (Types.ValueTypes e) (Types.ValueTypes s) then
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
                if isLeftSupertypeOfRight (Types.ValueTypes i) (Types.ValueTypes e) then
                    Must i |> Ok
                elif isLeftSupertypeOfRight (Types.ValueTypes e) (Types.ValueTypes i) then
                    Must e |> Ok
                else
                    Error [IncomparableReturnTypes(pos, i, e)]
            | May i, Must e
            | Must i, May e
            | May i, May e ->
                if isLeftSupertypeOfRight (Types.ValueTypes i) (Types.ValueTypes e) then
                    May i |> Ok
                elif isLeftSupertypeOfRight (Types.ValueTypes e) (Types.ValueTypes i) then
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
            if isLeftSupertypeOfRight (Types.ValueTypes retType) (Types.ValueTypes f) then Ok retType
            else Error [ReturnTypeMismatch (pos, retType, Types.ValueTypes f)]
        | May f -> Error [MayOrMayNotReturn (pos, retType, f)]
        )


/// Checks whether the lists of statements does not contain any synchronous
/// statements. This check is required for function bodies.
let private checkAbsenceOfSyncStmts stmts = 
    let rec checkAbsenceOfSyncStmt oneStmt =
        let checkStmts =
            List.map checkAbsenceOfSyncStmt
            >> contract
            >> Result.bind (fun _ -> Ok ()) // in case we succeeded on every 
                                            // statement, simply indicate success
        match oneStmt with
        // atomic imperative statements are Ok
        | Stmt.VarDecl _ | Assign _ | Assert _ | Assume _ | Stmt.Print _
        | FunctionCall _ | Return _ ->
            Ok ()
        | Stmt.ExternalVarDecl v ->
            Error [ExternalsInFunction v.pos]
        // synchronous statements
        | Await (p,_) | ActivityCall (p,_,_,_,_) | Preempt (p,_,_,_,_) | Cobegin (p,_)
        | RepeatUntil (p,_,_, true) -> // since we do not have 'break', there is now way to end a endless loop from within
            Error [SynchronousStatementInFunction p]
        // imperative statements containing statements
        | StmtSequence stmts | WhileRepeat (_, _, stmts) 
        | RepeatUntil (_, stmts, _, false) -> 
            checkStmts stmts
        | ITE (_, _, ifBranch, elseBranch) ->
            ifBranch @ elseBranch |> checkStmts

    checkAbsenceOfSyncStmt (StmtSequence stmts)


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
              typ = Types.ValueTypes BoolType; 
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
let rec private fDataType lut utyDataType =
    match utyDataType with
    // simple types
    | AST.BoolType _ -> Types.ValueTypes BoolType |> Ok
    | AST.SignedType (size, _, _) -> IntType size |> Types.ValueTypes |> Ok
    | AST.UnsignedType (size, _, _) -> UintType size |> Types.ValueTypes |> Ok
    | AST.FloatType (size, _, _) -> FloatType size |> Types.ValueTypes |> Ok
    // structured types
    | AST.ArrayType (size, elemDty, pos) ->
        let ensurePositive num =
            if num > 0 then Ok num
            else Error [PositiveSizeExpected(pos, num)]
        let checkSize =
            checkExpr lut 
            >> Result.bind (evalCompTimeInt lut)
            >> Result.bind ensurePositive
        checkSize size
        |> Result.bind(fun checkedSize ->
            fDataType lut elemDty
            |> Result.bind(fun dty -> 
                match dty with
                | ValueTypes sth ->
                    ArrayType (checkedSize, sth)
                    |> Types.ValueTypes
                    |> Ok 
                | _ -> Error [ValueArrayMustHaveValueType pos]
                )
            )
    | AST.TypeName spath ->
        // look up given static name in the dict of known named types (user types)
        let found, typ =
            lut.ncEnv.spathToQname spath
            |> lut.userTypes.TryGetValue
        if found then Ok typ
        else failwith <| sprintf "Did not find a type under the name %s." spath.dottedPathToString
    // unsupported now:
    | AST.BitvecType _
    | AST.SliceType _
    | AST.Signal _ -> 
        Error [UnsupportedFeature (utyDataType.Range, "types other than bool, int, uint, float, fixed size array or user defined struct")]


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
let private fFunPrototype lut pos name inputs outputs retType annotation =
    let createFunPrototype ((((qname, ins), outs), ret), annotation) = 
        let funPrototype =
            {
                FunctionPrototype.pos = pos
                isFunction = true
                name = qname
                inputs = ins
                outputs = outs
                returns = ret
                annotation = annotation
                allReferences = HashSet()
            }
        do addDeclToLut lut qname (Declarable.FunctionPrototype funPrototype)
        funPrototype

    // check that it is a first class type
    let checkReturn rets  =
        match rets with
        | None -> Void |> Ok
        | Some ret ->
            ret |> Result.bind (
                function
                | Types.ValueTypes f -> f |> Ok 
                | _ -> Error [MustReturnFirstClassType (pos, name.id)]
                )

    Ok (lut.ncEnv.nameToQname name)
    |> combine <| contract inputs
    |> combine <| contract outputs
    |> combine <| checkReturn retType
    |> combine <| annotation
    |> Result.map createFunPrototype


/// Type check a sub program
let private fSubProgram lut pos isFunction name inputs outputs retType body annotation =
    let createSubProgram (((((qname, ins), outs), ret), stmts), annotation) = 
        let funact =
            {
                SubProgramDecl.isFunction = isFunction
                pos = pos
                name = qname
                inputs = ins
                outputs = outs
                body = stmts
                returns = ret
                annotation = annotation
                allReferences = HashSet()
            }
        do addDeclToLut lut qname (Declarable.SubProgramDecl funact)
        funact
    // check that there is only one return value and it is a first class type
    let checkReturn rets bodyContractionRes =
        match rets with
        | None -> Void |> Ok
        | Some ret ->
            ret |> Result.bind (
                function
                | Types.ValueTypes f -> f |> Ok 
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
            |> Result.bind checkAbsenceOfSyncStmts
            |> Result.bind (fun _ -> cb) // if no synchronous statements were found, return the contracted body
        else
            cb
            |> Result.bind (checkStmtsWillPause pos name)
            |> Result.bind (fun _ -> cb) // if there is no instantaneous path, return the contracted body
    
    Ok (lut.ncEnv.nameToQname name)
    |> combine <| contract inputs
    |> combine <| contract outputs
    |> combine <| checkReturn retType contractedBody
    |> combine <| contractedBody
    |> combine <| annotation
    |> Result.map createSubProgram


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
        |> List.map (Result.bind (fun v -> if v.datatype.IsValueType() then Ok v else Error[ValueStructContainsRef (std.name, v)]))
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
                >> ReferenceTypes.StructType >> Types.ReferenceTypes )
        else
            // create value type
            Ok qname
            |> combine <| checkValueFields std.fields
            |> Result.map (
                fun (q, f) -> (std.name.Range, q, f)
                >> ValueTypes.StructType >> Types.ValueTypes )
    // add type declaration to lookup table
    match newType with
    | Ok typ -> do addTypeToLut lut qname typ
    | _ -> ()
    newType

        
let private fNewTypeDecl pos = unsupported4 "new type declarations" pos //TODO
let private fTypeAliasDecl pos = unsupported4 "alias declarations" pos //TODO
let private fEnumTypeDecl (etd: AST.EnumTypeDecl) = unsupported1 "enum declarations" etd.range //TODO 
let private fUnitDecl pos = unsupported4 "unit declarations" pos //TODO
let private fClockDecl (cld: AST.ClockDecl) = unsupported1 "clock declarations" cld.range //TODO


//=============================================================================
// Define all actions for AST transformation and do the type checking
//=============================================================================

let private fAssign lut pos lhs rhs =
    let createAssign myleft (myright: TypedRhs) =
        amendRhsExpr false myleft.typ myright
        |> Result.map (fun amendedRight -> Assign (pos, myleft, amendedRight))
    
    lhs
    |> combine <| rhs
    |> Result.bind (fun (l, r) -> 
        if isLhsMutable lut l.lhs then createAssign l r
        else Error [AssignmentToImmutable (pos, l.ToString())]
        )


let private generateVC isAssertion pos conditions msgOpt =
    let createAssume guards =
        let guard = // conjunction of given guards
            match guards with
            | [] -> failwith "Making an empty VC should be impossible!"
            | [g] -> g
            | g::gg ->
                List.foldBack (fun e acc -> {rhs = Conj(e, acc); typ = Types.ValueTypes BoolType; range = pos}) gg g
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
            {rhs = BoolConst false; typ = Types.ValueTypes BoolType; range = pos} |> Ok
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


let private fActCall = checkActCall


let private fFunCall lut pos fp inputs outputs =
    checkFunCall true lut pos fp inputs outputs
    |> Result.map(fun ((n, i, o), _) -> FunctionCall (pos, n, i, o))


let private fEmit = unsupported2 "event emissions" //TODO


/// Check that type of returned expression fits the declared return type of a subprogram
/// retTypOpt is the declared return type of the subprogram (None corresponds to void)
/// exprOpt is the expression of the return statement (None corresponds to empty return)
let private fReturn retTypOpt pos exprOpt =
    match retTypOpt, exprOpt with
    | None, None -> Return (pos, None) |> Ok
    | Some retTyp, Some expr ->
        combine retTyp expr 
        |> Result.bind (fun (r, e) -> amendRhsExpr true r e)
        |> Result.bind (fun (e: TypedRhs) -> match e.typ with | Types.ValueTypes _ -> Ok e | _ -> Error [NonFirstClassReturnStmt pos])
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
    | AST.ActivityCall (range, optLhs, pname, inputOptList, outputOptList) ->
        fActCall lut range pname
        <| Option.map (checkAssignLExpr lut) optLhs
        <| List.map (checkExpr lut >> Result.map(tryEvalConst lut)) inputOptList
        <| List.map (checkLExpr lut) outputOptList
    | ASTStmt.FunctionCall (range, pname, inputOptList, outputOptList) ->
        fFunCall lut range pname
        <| List.map (checkExpr lut >> Result.map(tryEvalConst lut)) inputOptList
        <| List.map (checkLExpr lut) outputOptList
    | AST.Emit(range, pname) ->
        fEmit range pname
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
        funacts: Collections.ResizeArray<Result<SubProgramDecl, TyCheckError list>>
        funPrototypes: Collections.ResizeArray<Result<FunctionPrototype, TyCheckError list>>
        variables: Collections.ResizeArray<Result<VarDecl, TyCheckError list>>
        externalVariables: Collections.ResizeArray<Result<ExternalVarDecl, TyCheckError list>>
        types: Collections.ResizeArray<Result<Types, TyCheckError list>>
        memberPragmas: ResizeArray<Result<Attribute.MemberPragma, TyCheckError list>>
        mutable entryPoint: Result<SubProgramDecl, TyCheckError list> option
    }
    member this.AddFunAct fa = this.funacts.Add fa
    member this.AddFunPrototype fp = this.funPrototypes.Add fp
    member this.AddVariable v = this.variables.Add v
    member this.AddExternalVariable v = this.externalVariables.Add v
    member this.AddType t = this.types.Add t
    member this.AddMemberPragma mp = this.memberPragmas.Add mp
            
    // TODO: Simplify this, fjg 19.01.19
    member this.UpdateEntryPoint (pack: AST.Package) (act: Result<SubProgramDecl, _>) =
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
            | Some ep, None when pack.IsLibrary ->
                Some (Error [IllegalEntryPoint (ep.pos, pack)])
            | Some ep, Some (Error err) when pack.IsLibrary ->
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
let public fPackage lut (pack: AST.Package) =
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
            | AST.Member.Nothing 
            | AST.Member.Import _ ->
                () // ignore these members
            | AST.Member.Pragma p ->
                do typedMembers.AddMemberPragma (Annotation.checkMemberPragma lut p)
            | AST.Member.EnumType e -> 
                do typedMembers.AddType (fEnumTypeDecl e)
            | AST.Member.StructType s -> 
                do typedMembers.AddType (fStructTypeDecl lut s)
            | AST.Member.NewType nt ->
                let t =
                    fNewTypeDecl nt.range nt.name
                    // <| fDataType lut nt.representation
                    <| Option.map (fDataType lut) nt.representation
                    <| Annotation.checkOtherDecl nt.annotations
                do typedMembers.AddType t
            | AST.Member.Type t ->
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
                    fSubProgram lut a.range a.isFunction a.name
                    <| List.map (recParamDecl lut) a.inputs
                    <| List.map (recParamDecl lut) a.outputs
                    <| retTypOpt
                    <| List.map (recStmt lut retTypOpt) a.body
                    <| Annotation.checkSubProgram a
                do typedMembers.AddFunAct funact
                do typedMembers.UpdateEntryPoint pack funact
            | AST.Member.Prototype f ->
                let funPrototype =
                    fFunPrototype lut f.range f.name
                    <| List.map (recParamDecl lut) f.inputs
                    <| List.map (recParamDecl lut) f.outputs
                    <| Option.map (recReturnDecl lut) f.result
                    <| Annotation.checkFunctionPrototype lut f
                do typedMembers.AddFunPrototype funPrototype
            processMembers typedMembers ms
        
    let createPackage (((((((modName, funPrototypes), funacts), variables), externalVariables), types), memberPragmas), entryPoint) =
    
        assert (List.length types = lut.userTypes.Count)
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
        processMembers typedMembers (pack.imports @ pack.members)
    
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
let typeCheck (pack: AST.Package, ncEnv: SymbolTable.LookupTable) =
    let lut = TypeCheckContext.Empty(ncEnv)
    fPackage lut pack
    |> function
        | Ok p -> 
            Blech.Common.Logging.log6 "Main" ("typed syntax tree built\n" + p.ToString())
            Ok (lut, p)
        | Error errs -> Error (Diagnostics.wrapErrsInLogger Diagnostics.Phase.Typing errs)
        