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

module Blech.Frontend.TyChkExpressions

open Blech.Common

open CommonTypes
open BlechTypes
open TyChecked
open TypeCheckContext
open TyChkAmendment


//=========================================================================
// Functions for checking type and expression properties
//=========================================================================

let private ensureCurrent (dname: AST.DynamicAccessPath) =
    match dname.timepoint with
    | AST.TemporalQualification.Current ->
        // While checkExpr tries to evaluate trivial expressions, it does NOT
        // however substitute names for values in constants.
        // This is the reason why there is a separate evalConst function 
        // that does exactly that.
        Ok dname
    | AST.TemporalQualification.Next _ 
    | AST.TemporalQualification.Previous _ -> 
        Error [NextPrevOnReturn dname.Range]


/// Checks that given expression consists of only a name (or reference)
let private isExprALocation expr = 
    match expr.rhs with
    | RhsStructure.RhsCur _ 
    | RhsStructure.Prev _ -> true
    | _ -> false
    

/// check that lhs is mutable
let internal isLhsMutable lut lhs =
    let rec isTmlMutable = function
    | Loc qname ->
        let found, declarable = lut.nameToDecl.TryGetValue qname
        if found then
            match declarable with
            | Declarable.VarDecl v -> v.mutability.Equals Mutability.Variable, v.datatype
            | Declarable.ParamDecl p -> p.isMutable, p.datatype
            | Declarable.ExternalVarDecl v -> v.mutability.Equals Mutability.Variable, v.datatype
            | Declarable.SubProgramDecl _
            | Declarable.FunctionPrototype _ ->
                failwith "Asking for mutability of a subprogram. That cannot be right."
        else
            failwith <| sprintf "Lhs %s not in nameToDecl" (qname.ToString())
    | FieldAccess (tml, ident) ->
        let ism, typ = isTmlMutable tml
        if ism then
            match typ with
            | Types.ValueTypes (ValueTypes.StructType (_, typname, typfields))
            | Types.ReferenceTypes (ReferenceTypes.StructType(_, typname, typfields)) ->
                typfields
                |> List.tryFind (fun f -> f.name.basicId = ident)
                |> function
                    | None -> failwith "Field not in struct. Should have been checked before."
                    | Some varDecl -> varDecl.mutability.Equals Mutability.Variable, varDecl.datatype
            | _ -> failwith "Trying to access a field of something that is not a struct. Should have been detected before."
        else
            false, typ
    | ArrayAccess (tml, idx) -> fst <| isTmlMutable tml, getDatatypeFromTML lut (ArrayAccess (tml, idx))

    match lhs with
    | Wildcard -> true
    | LhsCur tml
    | LhsNext tml -> fst <| isTmlMutable tml


/// Returns true when the evaluation of expr does not change the program's state
let rec private hasNoSideEffect expr =
    let recurFields fields =
        fields
        |> List.map (snd >> hasNoSideEffect)
        |> List.forall id
    match expr.rhs with
    // locations
    | RhsCur tml 
    | Prev tml -> tml.FindAllIndexExpr |> List.forall hasNoSideEffect
    // constants and literals
    | BoolConst _ | IntConst _ | BitsConst _ | FloatConst _  | ResetConst _ -> true
    | StructConst fields -> recurFields fields
    | ArrayConst elems -> recurFields elems
    // call, has no side-effect IFF it does not write any outputs
    // this assumption is only valid when there are not global variables (as is the case in Blech)
    // and no external C variables are written (TODO!)
    | FunCall (_, _, outputs) -> outputs = []
    // unary 
    | Neg e | Bnot e -> hasNoSideEffect e
    // logical
    | Conj (x, y) | Disj (x, y) 
    // bitwise 
    | Band (x, y) | Bor (x, y) | Bxor (x, y)
    | Shl (x, y) | Shr (x, y) | Sshr (x, y) | Rotl (x, y) | Rotr (x, y)
    // relational
    | Les (x, y) | Leq (x, y) | Equ (x, y)
    // arithmetic
    | Add (x, y) | Sub (x, y) | Mul (x, y) | Div (x, y) | Mod (x, y) -> 
        hasNoSideEffect x && hasNoSideEffect y


/// True if given expression contains only compile time or param values
let rec internal isStaticExpr lut expr =
    let recurFields fields =
        fields
        |> List.map (snd >> (isStaticExpr lut))
        |> List.forall id
    match expr.rhs with
    // locations
    | RhsCur tml -> 
        match lut.nameToDecl.[tml.QNamePrefix].TryGetMutability with
        | None -> failwith "Error. A typed memory location must have some mutability information."
        // const and param - static
        | Some Mutability.CompileTimeConstant
        | Some Mutability.StaticParameter -> true
        // let and var - dynamic
        | Some Mutability.Immutable
        | Some Mutability.Variable -> false
    | Prev _ -> false // prev exists only on var
    | BoolConst _ | IntConst _ | BitsConst _ | FloatConst _ | ResetConst _ -> true
    | StructConst fields -> recurFields fields
    | ArrayConst elems -> recurFields elems
    | FunCall _ -> false // we do not have compile time functions yet
    // unary 
    | Neg e | Bnot e -> isStaticExpr lut e
    // logical
    | Conj (x, y) | Disj (x, y) 
    // bitwise
    | Band (x, y) | Bor (x, y) | Bxor (x, y) 
    | Shl (x, y) | Shr (x, y) | Sshr (x, y) | Rotl (x, y) | Rotr (x, y)
    // relational
    | Les (x, y) | Leq (x, y) | Equ (x, y)
    // arithmetic
    | Add (x, y) | Sub (x, y) | Mul (x, y) | Div (x, y) | Mod (x, y) -> 
        isStaticExpr lut x && isStaticExpr lut y


/// Get float values for a and b, combine them using op,
/// wrap them back into FloatConst objects, taking original
/// precision into account
/// This operation may introduce rounding imprecision!
//let private combineFloat (a: FloatConst) (b: FloatConst) op =
//    let wrapFloat a b (res: float) =
//        let combinePrecision a b =
//            match a, b with
//            | FloatConst.Single _, FloatConst.Single _ -> FloatConst.Single
//            // return double if there was at least one double
//            | _,_ -> FloatConst.Double

//        res
//        |> floatToString
//        |> combinePrecision a b
//        |> FloatConst

//    op a.ToFloat b.ToFloat
//    |> wrapFloat a b

let private add this that =
    match this.rhs, that.rhs with
    | IntConst a, IntConst b -> IntConst (a + b)
    | FloatConst a, FloatConst b -> FloatConst <| Float.Arithmetic (+) a b
    | _ -> Add(this, that)

let private mul this that =
    match this.rhs, that.rhs with
    | IntConst a, IntConst b -> IntConst (a * b)
    | FloatConst a, FloatConst b -> FloatConst <| Float.Arithmetic (*) a b
    | _ -> Mul(this, that)

let private div this that =
    match this.rhs, that.rhs with
    | IntConst a, IntConst b -> IntConst (a / b)
    | FloatConst a, FloatConst b -> FloatConst <| Float.Arithmetic (/) a b
    | _ -> Div(this, that)

let private sub this that =
    match this.rhs, that.rhs with
    | IntConst a, IntConst b -> IntConst (a - b)
    | FloatConst a, FloatConst b -> FloatConst <| Float.Arithmetic (-) a b
    | _ -> Sub(this, that)

let private modus this that =
    match this.rhs, that.rhs with
    | IntConst a, IntConst b -> IntConst (a % b)
    | FloatConst a, FloatConst b -> failwith "modulo operation on float should not occur" // this is checked before calling this function, so this line is basically dead code
    | _ -> Mod(this, that)

let private neg this =
    match this.rhs with
    | BoolConst b -> BoolConst (not b)
    | Neg b -> b.rhs
    | Bxor (a,b) -> Equ (a, b) // this is not idempotent
    | _ -> Neg this

let private conj this that =
    match this.rhs, that.rhs with
    | BoolConst false, _ -> BoolConst false // optimisation, note "and then" semantics prohibits to do the same in case of _, false
    | BoolConst true, t
    | t, BoolConst true -> t
    | _ -> Conj(this, that)

let private disj this that =
    match this.rhs, that.rhs with
    | BoolConst false, t -> t
    | t, BoolConst false -> t
    | BoolConst true, _ -> BoolConst true // optimisation, note "and then" semantics prohibits to do the same in case of _, true
    | _ -> Disj(this, that)

let private bxor this that =
    match this.rhs, that.rhs with
    | BoolConst a, BoolConst b -> BoolConst (a <> b) //covers the case where both are true, NOT redundant as above for conj and disj
    | BoolConst false, t
    | t, BoolConst false -> t
    | _ -> Bxor(this, that)

let private less this that =
    match this.rhs, that.rhs with
    | BoolConst a, BoolConst b -> BoolConst (a < b)
    | IntConst a, IntConst b -> BoolConst (a < b)
    | BitsConst a, BitsConst b -> BoolConst <| Bits.Relational (<) a b
    | FloatConst a, FloatConst b -> BoolConst <| Float.Relational (<) a b
    | _ -> Les(this, that)

let private leq this that =
    match this.rhs, that.rhs with
    | BoolConst a, BoolConst b -> BoolConst (a <= b)
    | IntConst a, IntConst b -> BoolConst (a <= b)
    | BitsConst a, BitsConst b -> BoolConst <| Bits.Relational (<=) a b
    | FloatConst a, FloatConst b -> BoolConst <| Float.Relational (<=) a b
    | _ -> Leq(this, that)

let private eq this that =
    match this.rhs, that.rhs with
    | BoolConst a, BoolConst b -> BoolConst (a = b)
    | IntConst a, IntConst b -> BoolConst (a = b)
    | BitsConst a, BitsConst b -> BoolConst <| Bits.Relational (=) a b
    | FloatConst a, FloatConst b -> BoolConst <| Float.Relational (=) a b
    | _ -> Equ(this, that)


//let rec private eq this that =
//    let checkField (id1, st1) (id2, st2) =
//        eq st1 st2
//        |> function
//            | BoolConst r -> r && id1 = id2
//            | _ -> false
    
//    let compareAssignments x y =
//        let sortedA = x |> List.sortBy fst
//        let sortedB = y |> List.sortBy fst
//        (sortedA, sortedB)
//        ||> List.forall2 (fun (id1,e1) (id2,e2) -> checkField (id1,e1) (id2,e2))
//        |> BoolConst

//    let compareComposite a b =
//        if isLiteral this && isLiteral that then
//            if List.length a = List.length b then
//                compareAssignments a b
//            else // we have literals where possibly one carries default value that the other does not
//                if this.typ = that.typ then
//                    let defaultComposite = 
//                        match getDefaultValueFor this.range "" this.typ with
//                        | Ok x -> x.rhs 
//                        | Error _ -> failwith "Failed to get default value for composite type."
//                    let explodedA = unsafeMergeCompositeLiteral defaultComposite this.rhs
//                    let explodedB = unsafeMergeCompositeLiteral defaultComposite that.rhs
//                    match explodedA, explodedB with
//                    | StructConst ea, StructConst eb -> compareAssignments ea eb
//                    | ArrayConst ea, ArrayConst eb -> compareAssignments ea eb
//                    | _ -> failwith "Structs exploded in unpredictable ways."
//                else
//                    failwith "incomparable struct sizes"
//        else
//            Equ(this, that)
    
//    match this.rhs, that.rhs with
//    | BoolConst a, BoolConst b -> BoolConst (a = b)
//    | IntConst a, IntConst b -> BoolConst (a = b)
//    | FloatConst a, FloatConst b -> BoolConst <| Float.Relational (=) a b
//    | ResetConst, ResetConst -> BoolConst true
//    | StructConst a, StructConst b -> compareComposite a b
//    | ArrayConst a, ArrayConst b -> compareComposite a b
//    | _ -> Equ(this, that)

/// Given a typed rhs expression, this function tries to evaluate this 
/// expression to a constant and return a new TypedRhs such that
/// isLiteral returns true on that.
/// However, it may return a non-constant expression if it cannot be
/// reduced. No error is thrown.
let rec internal tryEvalConst lut (checkedExpr: TypedRhs) : TypedRhs =
    let evalBin x y f =
        let newrhs = tryEvalConst lut x |> f <| tryEvalConst lut y
        { rhs = newrhs; typ = checkedExpr.typ; range = checkedExpr.Range }
        //|> Result.bind f
    let recurFields constBuilder fs =
        let kvps = fs |> List.map (fun (i,f) -> i, tryEvalConst lut f)
        { rhs = constBuilder kvps
          typ = checkedExpr.typ
          range = checkedExpr.Range }
    match checkedExpr.rhs with
    // simple literal
    | IntConst _ | BoolConst _ | BitsConst _ | FloatConst _ | ResetConst -> checkedExpr
    // composite literal
    | StructConst fields -> recurFields StructConst fields
    | ArrayConst fields -> recurFields ArrayConst fields
    // arithmetic
    | Add (x, y) -> evalBin x y add 
    | Sub (x, y) -> evalBin x y sub 
    | Mul (x, y) -> evalBin x y mul 
    | Div (x, y) -> evalBin x y div 
    | Mod (x, y) -> evalBin x y modus
    // unary
    | Bnot x  // todo: go on here
    | Neg x -> 
        let newRhs = tryEvalConst lut x |> neg
        { rhs = newRhs; typ = checkedExpr.typ; range = checkedExpr.Range }
    // logical
    | Conj (x, y) -> evalBin x y conj
    | Disj (x, y) -> evalBin x y disj
    // bitwise
    | Band (x, y) // todo: go on here
    | Bor (x, y)
    | Shl (x, y)
    | Shr (x, y)
    | Sshr (x, y)
    | Rotl (x, y)
    | Rotr (x, y)
    | Bxor (x, y) -> evalBin x y bxor 
    // relational
    | Les (x, y) -> evalBin x y less 
    | Leq (x, y) -> evalBin x y leq
    | Equ (x, y) -> evalBin x y eq 
    // function calls
    | FunCall (name, ins, outs) ->
        let newIns = ins |> List.map (tryEvalConst lut)
        { rhs = FunCall (name, newIns, outs); typ = checkedExpr.typ; range = checkedExpr.Range }
    | Prev _ -> checkedExpr // prev is a location and never constant
    | RhsCur tml ->
        match lut.nameToDecl.[tml.QNamePrefix] with
        | Declarable.VarDecl v ->
            if v.mutability.Equals Mutability.CompileTimeConstant then
                match getInitValueForTml lut tml with
                | Ok trhs -> trhs // is constant by definition
                | Error _ -> checkedExpr // the tml access fails for arr[foo], where foo is not a compile time const
            else
                checkedExpr
        //| Declarable.ParamDecl _ -> Error [] // params not compile time const
        | _ -> checkedExpr


/// This tries to evaluate expr to a constant value
/// and returns a MustBeConst error if this operation fails.
and internal evalConst lut expr =
    let res = tryEvalConst lut expr
    if isConstantExpr lut res then Ok res
    else Error[MustBeConst(expr)]


/// This tries to evaluate expr to a constant integer value
/// and returns a MustBeConst error if the input is not constant
/// and returns a NotACompileTimeInt if the result is not an integer.
and internal evalCompTimeInt lut expr =
    evalConst lut expr
    |> Result.bind (fun constExpr ->
        match constExpr.rhs with
        | IntConst i -> Ok <| (int)i
        | _ -> Error [NotACompileTimeInt expr]
    )


/// Retrieves the initial value for a given TML
/// Returns an error, if the TML is an array access where the index is not constant
/// This is not the default value of the TML's data type but whatever was the rhs of the declaration.
and getInitValueForTml lut tml =
    // this step is necessary as for literal initialisers we cannot take the 
    // datatype of the initialiser - that could be Any
    // instead we return the datatype of the declaration which is concrete
    let thisDty = getDatatypeFromTML lut tml
    match tml with
    | Loc qname ->
        let initValue = 
            match lut.nameToDecl.[qname].TryGetDefault() with
            | Some x -> x
            | None -> failwith "Compiler bug. Could not get obtain the default value of a location."
        { rhs = initValue.rhs
          typ = thisDty
          range = initValue.Range } |> Ok
    | FieldAccess (tml, ident) -> 
        getInitValueForTml lut tml
        |> Result.bind (fun v ->
            match v.rhs with
            | StructConst assignments ->
                assignments
                // now it may happen that this identifier does not exist in the default literal, get default value
                |> List.tryFind (fun e -> fst e = ident)
                |> function
                    | Some e -> snd e |> Ok // found an initialiser, return that
                    | None ->               // nope, get default value for that field
                        match v.typ with
                        | ValueTypes (ValueTypes.StructType (_, _, fields)) ->
                            fields 
                            |> List.find (fun vdecl -> vdecl.name.basicId = ident)
                            |> (fun vdecl -> getInitValueWithoutZeros Range.range0 "" vdecl.datatype)
                        | _ -> failwith "This must be a value struct here."
            | _ -> failwith "Impossible. StructConst must be the result for a getInitValue on a FieldAccess."
            )
    | ArrayAccess (tml, idx) ->
        getInitValueForTml lut tml
        |> Result.bind (fun v ->
            match v.rhs with
            | ArrayConst lst ->
                evalCompTimeInt lut idx
                |> Result.bind (fun constIdx ->
                    // either the value for that index is user defined, or return a default value for the element type
                    lst
                    |> List.tryFind (fun e -> fst e = constIdx)
                    |> function
                        | Some e -> snd e |> Ok // found an initialiser, return that
                        | None ->               // nope, get default value for that cell
                            match v.typ with
                            | ValueTypes (ArrayType (_, elemTyp)) -> getInitValueWithoutZeros Range.range0 "" (ValueTypes elemTyp)
                            | _ -> failwith "This must be a value array here."
                    )
            | _ -> failwith "Impossible. ArrayConst must be the result for a getInitValue on an ArrayAccess."
            )


//=========================================================================
//  Functions that construct typed expressions from subexpressions
//=========================================================================


/// Checks if literals and constant expression are of suitable size.
let private adoptAnyToTargetExpr (anyExpr: TypedRhs) (targetExpr: TypedRhs) : TyChecked<TypedRhs> =
    match anyExpr.typ, targetExpr.typ with
    | AnyInt value, ValueTypes (IntType intX) ->
        if intX.CanRepresent value then
            Ok {anyExpr with typ = ValueTypes (IntType intX)}
        else
            Error[SameTypeRequired (anyExpr, targetExpr)]  // TODO: better error message, fjg. 28.01.20            
    
    | AnyInt value, ValueTypes (NatType natX) ->
        if natX.CanRepresent value then
            Ok {anyExpr with typ = ValueTypes (NatType natX)}
        else
            Error[SameTypeRequired (anyExpr, targetExpr)]  // TODO: better error message, fjg. 28.01.20
    
    | AnyBits value, ValueTypes (BitsType bitX) ->
        if bitX.CanRepresent value then
            Ok {anyExpr with typ = ValueTypes (BitsType bitX)}
        else
            Error[SameTypeRequired (anyExpr, targetExpr)]  // TODO: better error message, fjg. 28.01.20
    
    | AnyBits value, ValueTypes (NatType natX) ->
        if natX.CanRepresent value then
            Ok {anyExpr with typ = ValueTypes (NatType natX)}
        else
            Error[SameTypeRequired (anyExpr, targetExpr)]  // TODO: better error message, fjg. 28.01.20
    
    | AnyFloat value, Types.ValueTypes (FloatType floatX) ->
        if floatX.CanRepresent value then
            Ok {anyExpr with typ = ValueTypes (FloatType floatX)}
        else
            Error[SameTypeRequired (anyExpr, targetExpr)]  // TODO: better error message, fjg. 28.01.20            
   
    | _, _, _  ->
        Ok anyExpr


// --------------------------------------------------------------------
// ---  Unary logical and - TODO - bitwise not
// --------------------------------------------------------------------

/// Given a typed expression, construct its negation.
/// If the type is not boolean, an error will be returned instead.
let private negate r (expr: TypedRhs) =
    match expr.typ with
    | Types.ValueTypes BoolType ->
        let structure = neg expr
        { rhs = structure;
          typ = Types.ValueTypes BoolType
          range = expr.Range } |> Ok
    | _ -> Error [ExpectedBoolCond (r, expr)]

/// Unsafe unaryMinus, we assume structure has arithmetic type. This must be
/// ensured by the caller.
let private unsafeUnaryMinus (expr: TypedRhs) = 
    match expr.typ with
    | ValueTypes (IntType _) ->
        match expr.rhs with
        | IntConst bi -> IntConst -bi
        | _ -> Sub ({expr with rhs = IntConst 0I}, expr) //0 - expr

    | ValueTypes (BitsType size) ->
        match expr.rhs with
        | BitsConst b -> BitsConst <| b.UnaryMinus size.MaxValue            // numeric wrap-around
        | _ -> Sub ({expr with rhs = BitsConst Bits.Zero}, expr) //0 - expr
        
    | AnyFloat _ 
    | ValueTypes (FloatType _) ->
        match expr.rhs with
        | FloatConst f -> FloatConst f.UnaryMinus 
        | _ -> Sub ({expr with rhs = FloatConst Float.Zero}, expr) //0 - expr
    | _ -> failwith "UnsafeUnaryMinus called with something other than int or float!"
    

/// Given a typed Expression, construct its negative.
/// If the type is not numeric, an error will be returned instead.
let private unaryMinus r (expr: TypedRhs) =
    match expr.typ with
    // no unary minus on natural number since it cannot be used anywhere
    | AnyInt value ->
        Ok { rhs = IntConst -value
             typ = AnyInt -value
             range = expr.range }
    | AnyFloat value ->
        Ok { rhs = unsafeUnaryMinus expr 
             typ = AnyFloat -value 
             range = expr.range }
    | ValueTypes (IntType _)
    | ValueTypes (BitsType _)
    | ValueTypes (FloatType _) ->
        Ok { expr with rhs = unsafeUnaryMinus expr }
    | _ -> // error illegal minus on expr
        Error [CannotInvertSign(r, expr)]

// --------------------------------------------------------------------
// ---  Logical Operators
// --------------------------------------------------------------------

/// Given two typed expressions, construct their binary logical operator.
/// If some of the types is not boolean, an error will be returned instead.
let private formLogical operator ((expr1: TypedRhs), (expr2: TypedRhs)) =
    match expr1.typ, expr2.typ with
    | Types.ValueTypes BoolType, Types.ValueTypes BoolType ->
        let structure = operator expr1 expr2
        { rhs = structure; 
          typ = Types.ValueTypes BoolType
          range = Range.unionRanges expr1.Range expr2.Range }
        |> Ok
    | _ -> Error [ExpectedBoolConds (expr1, expr2)]
    
/// Given two typed expressions, construct their conjunction.
/// If some of the types is not boolean, an error will be returned instead.
//let private formConjunction ((expr1: TypedRhs), (expr2: TypedRhs)) =
//    match expr1.typ, expr2.typ with
//    | Types.ValueTypes BoolType, Types.ValueTypes BoolType ->
//        let structure = conj expr1 expr2
//        { rhs = structure; 
//          typ = Types.ValueTypes BoolType
//          range = Range.unionRanges expr1.Range expr2.Range } |> Ok
//    | _ -> Error [ExpectedBoolConds (expr1, expr2)]

let private formConjunction = formLogical conj

/// Given two typed expressions, construct their disjunction.
/// If some of the types is not boolean, an error will be returned instead.
//let private formDisjunction ((expr1: TypedRhs), (expr2: TypedRhs)) =
//    match expr1.typ, expr2.typ with
//    | Types.ValueTypes BoolType, Types.ValueTypes BoolType ->
//        let structure = disj expr1 expr2
//        { rhs = structure; 
//          typ = Types.ValueTypes BoolType
//          range = Range.unionRanges expr1.Range expr2.Range } |> Ok
//    | _ -> Error [ExpectedBoolConds (expr1, expr2)]

let private formDisjunction = formLogical disj

/// Given two typed expressions, construct their exclusive disjunction.
/// If some of the types is not boolean, an error will be returned instead.
//let private formXor ((expr1: TypedRhs), (expr2: TypedRhs)) =
//    match expr1.typ, expr2.typ with
//    | Types.ValueTypes BoolType, Types.ValueTypes BoolType ->
//        let structure = bxor expr1 expr2
//        { rhs = structure; 
//          typ = Types.ValueTypes BoolType
//          range = Range.unionRanges expr1.Range expr2.Range }
//        |> Ok
//    | _ -> Error [ExpectedBoolConds (expr1, expr2)]


// --------------------------------------------------------------------
// ---  TODO: Logical Operators, fjg. 21.01.20
// --------------------------------------------------------------------

let private formXor = formLogical bxor

/// Given two typed expressions, construct their equality.
/// If the two types are not comparable, an error will be returned instead.
/// Assuming that expressions are reduced to literals before calling this function -
/// makes a difference for complex data types!
let private formEquality ((expr1: TypedRhs), (expr2: TypedRhs)) : TyChecked<TypedRhs> =
    let resultOk okCase = { rhs = okCase 
                            typ = Types.ValueTypes BoolType
                            range = Range.unionRanges expr1.Range expr2.Range }
    match expr1.typ, expr2.typ with
    // we allow to compare numbers of different sizes, which technically are of different type
    | Types.ValueTypes BoolType, Types.ValueTypes BoolType
    | Types.AnyInt _, Types.AnyInt _
    | Types.ValueTypes (IntType _), Types.ValueTypes (IntType _)
    | Types.ValueTypes (IntType _), Types.AnyInt _
    | Types.AnyInt _, Types.ValueTypes (IntType _)
    | Types.ValueTypes (NatType _), Types.ValueTypes (NatType _)
    | Types.ValueTypes (NatType _), Types.AnyInt _
    | Types.AnyInt _, Types.ValueTypes (NatType _)
    | Types.ValueTypes (FloatType _), Types.ValueTypes (FloatType _) ->
        eq expr1 expr2 |> resultOk |> Ok
    | Types.ValueTypes lType, Types.ValueTypes rType when lType = rType ->
        if isLiteral expr1 && isLiteral expr2 then
            eq expr1 expr2 |> resultOk |> Ok
        else
            // disallow runtime comparison of structured values using ==
            Error[NoComparisonAllowed(expr1, expr2)]
    | _ -> Error [SameTypeRequired (expr1, expr2)]


/// Given two typed expressions, construct their inequality.
/// We assume that ineqFun is either 'less' or 'leq' from above.
/// If the two types are not comparable, an error will be returned instead.
//let private inequality ineqFun ((expr1: TypedRhs), (expr2: TypedRhs)) =
//    match expr1.typ, expr2.typ with
//    | Types.ValueTypes (IntType _), Types.AnyInt _
//    | Types.AnyInt _, Types.ValueTypes (IntType _)
    
//    | Types.ValueTypes (NatType _), Types.AnyInt _
//    | Types.AnyInt _, Types.ValueTypes (NatType _)
    
//    | Types.ValueTypes (NatType _), Types.AnyInt _
//    | Types.AnyInt _, Types.ValueTypes (NatType _)
    
//    | Types.AnyInt _, Types.AnyInt _
//    | Types.AnyFloat _, Types.AnyFloat _
//    | Types.ValueTypes BoolType, Types.ValueTypes BoolType
//    | Types.ValueTypes (IntType _), Types.ValueTypes (IntType _)
//    | Types.ValueTypes (NatType _), Types.ValueTypes (NatType _)
//    | Types.ValueTypes (FloatType _), Types.ValueTypes (FloatType _) ->
//        { rhs = ineqFun expr1 expr2
//          typ = Types.ValueTypes BoolType
//          range = Range.unionRanges expr1.Range expr2.Range }
//        |> Ok
//    | _ -> Error [SameArithmeticTypeRequired (expr1, expr2)]

/// Given two typed expressions, construct their strict inequality.
/// If the two types are not comparable, an error will be returned instead.
// let private lessThan = inequality less

/// Given two typed expressions, construct their inequality.
/// If the two types are not comparable, an error will be returned instead.
// let private lessEqualThan = inequality leq


// --------------------------------------------------------------------
// ---  Relational Operators
// --------------------------------------------------------------------

/// Given two typed expressions, construct their relation.
/// We assume that operator is either 'less', 'leq', or 'eq' from above.
/// If the two types are not comparable, an error will be returned instead.
let private combineRelationalOp op ((expr1: TypedRhs), (expr2: TypedRhs)) =
    match expr1.typ, expr2.typ with    
    | AnyInt _, AnyInt _
    | AnyFloat _, AnyFloat _
    | AnyBits _, AnyBits _
    | ValueTypes BoolType, ValueTypes BoolType
    | ValueTypes (IntType _), ValueTypes (IntType _)
    | ValueTypes (NatType _), ValueTypes (NatType _)
    | ValueTypes (BitsType _), ValueTypes (BitsType _)
    | ValueTypes (FloatType _), ValueTypes (FloatType _) -> 
        Ok { rhs = op expr1 expr2; typ = ValueTypes BoolType; range = Range.unionRanges expr1.Range expr2.Range }

    | _, _
        -> Error [SameArithmeticTypeRequired (expr1, expr2)]  // TODO: Same relational type required, fjg. 29.01.20


let private checkRelational operator (expr1: TypedRhs) (expr2: TypedRhs) =
    let e1 = adoptAnyToTargetExpr expr1 expr2
    let e2 = adoptAnyToTargetExpr expr2 expr1

    combine e1 e2
    |> Result.bind (combineRelationalOp operator)


/// Given two typed expressions, construct their strict inequality.
/// If the two types are not comparable, an error will be returned instead.
let private lessThan ((expr1: TypedRhs), (expr2: TypedRhs)) = checkRelational less expr1 expr2

/// Given two typed expressions, construct their inequality.
/// If the two types are not comparable, an error will be returned instead.
let private lessEqualThan ((expr1: TypedRhs), (expr2: TypedRhs)) = checkRelational leq expr1 expr2

/// Given two typed expressions, construct their equality.
/// If the two types are not comparable, an error will be returned instead.
/// Composite literals are currently not compared for equality.
let private equal ((expr1: TypedRhs), (expr2: TypedRhs)) = checkRelational eq expr1 expr2


// --------------------------------------------------------------------
// ---  Arithmetic Operators
// --------------------------------------------------------------------

/// Given two typed expressions and a combination function indicator
/// return a new typed expression as a combination of the two.
/// In case of type mismatches an error is returned instead.
let private combineArithmeticOp operator (expr1: TypedRhs, expr2: TypedRhs) =

    let rhs = operator expr1 expr2
    let rng = Range.unionRanges expr1.Range expr2.Range
    let commonSize size1 size2 = if size1 >= size2 then size1 else size2
    
    let typ = 
        match expr1.typ, expr2.typ with
        | ValueTypes (IntType size1), ValueTypes (IntType size2) ->
            Ok <| ValueTypes (IntType (commonSize size1 size2))
        | ValueTypes (NatType size1), ValueTypes (NatType size2) ->
            Ok <| ValueTypes (NatType (commonSize size1 size2)) 
        | ValueTypes (BitsType size1), ValueTypes (BitsType size2) ->
            Ok <| ValueTypes (BitsType (commonSize size1 size2)) 
        | ValueTypes (FloatType size1), ValueTypes (FloatType size2) ->
            Ok <| ValueTypes (FloatType (commonSize size1 size2))
        | AnyInt _, AnyInt _ ->
            let combinedValues = 
                match rhs with
                | IntConst res -> res
                | _ -> failwith "Combination of numbers resulted in not a number" //cannot happen
            Ok <| AnyInt combinedValues
        | AnyFloat _, AnyFloat _ ->
            let combinedValue = 
                match rhs with
                | FloatConst cv -> cv.value
                | _ -> failwith "Combination of numbers resulted in not a number" //cannot happen
            Ok <| AnyFloat combinedValue
        | t1, t2 when t1 = t2 -> 
            Error [MustBeNumeric(expr1, expr2)]
        | _ -> 
            Error [SameTypeRequired (expr1, expr2)]

    typ |> Result.bind (fun t -> Ok {rhs = rhs; typ = t; range = rng})


/// Checks if literals and constant expression are of suitable size.
let private checkArithmetic operator (expr1: TypedRhs) (expr2: TypedRhs) =
    let e1 = adoptAnyToTargetExpr expr1 expr2
    let e2 = adoptAnyToTargetExpr expr2 expr1

    combine e1 e2
    |> Result.bind (combineArithmeticOp operator)


/// Returns the addition of two typed expressions or an error in case of type mismatch.
let private addition ((expr1: TypedRhs), (expr2: TypedRhs)) = checkArithmetic add expr1 expr2


/// Returns the subtraction of two typed expressions or an error in case of type mismatch.
let private subtraction ((expr1: TypedRhs), (expr2: TypedRhs)) = checkArithmetic sub expr1 expr2


/// Returns the product of two typed expressions or an error in case of type mismatch.
let private product ((expr1: TypedRhs), (expr2: TypedRhs)) = checkArithmetic mul expr1 expr2


/// Returns the quotient of two typed expressions or an error in case of type mismatch.
let private quotient ((expr1: TypedRhs), (expr2: TypedRhs)) = checkArithmetic div expr1 expr2


/// Returns the remainder of integer division of two typed expressions or an error in case of type mismatch.
let private remainder ((expr1: TypedRhs), (expr2: TypedRhs)) = 
    match expr1.typ, expr2.typ with
    | ValueTypes (FloatType _), ValueTypes (FloatType _)
    | AnyFloat _, ValueTypes (FloatType _)
    | ValueTypes (FloatType _), AnyFloat _
    | AnyFloat _, AnyFloat _ ->
        Error [CannotModFloats (expr1, expr2)]
    | _ -> checkArithmetic modus expr1 expr2

        
//=============================================================================
// Checking right and left hand side usages (expressions)
// A function call can be the rhs of an expression and is hence tightly coupled
// with checkExpr.
//=============================================================================

/// Check that arguments in the output position match the number and type of
/// the formal parameters.
let private checkOutputs (lut: TypeCheckContext) pos (outputArgs: Result<_,_> list) declName (outputParams: ParamDecl list) =
    let rec typecheckOutputs = function
        | [] -> []
        | (paramDecl, (argExpr: TypedLhs))::ls -> 
            if argExpr.typ = paramDecl.datatype then // Given location must have the same type as formal output parameter for proper reading and writing from within the callee (10.04.18)
                if argExpr.lhs.Equals Wildcard then 
                    Error [ExprMustBeALocationL (pos, argExpr)] :: typecheckOutputs ls
                else
                    if isLhsMutable lut argExpr.lhs then
                        Ok argExpr :: typecheckOutputs ls
                    else
                        Error [ImmutableOutArg(pos, argExpr)] :: typecheckOutputs ls    
            else
                Error [ArgTypeMismatchL (pos, paramDecl, argExpr)] :: typecheckOutputs ls
    if outputArgs.Length = outputParams.Length then
        contract outputArgs
        |> Result.bind(List.zip outputParams >> typecheckOutputs >> contract)
    else
        Error [MismatchArgNum (pos, declName.ToString(), outputArgs.Length, outputParams.Length)]


/// Check that arguments in the input position match the number and type of
/// the formal parameters.        
let private checkInputs pos (inputArgs: Result<_,_> list) declName (inputParams: ParamDecl list) =
    let rec typecheckInputs = function
        | [] -> []
        | (argDecl, (expr: TypedRhs))::ls -> 
            match amendRhsExpr true argDecl.datatype expr with // this behaves like an initialisation
            | Ok amendedExpr ->
                if argDecl.datatype.IsValueType() || isExprALocation amendedExpr then
                    Ok amendedExpr :: typecheckInputs ls
                else
                    Error [ExprMustBeALocationR (pos, expr)] :: typecheckInputs ls
            | Error e ->
                Error e :: typecheckInputs ls
    if inputArgs.Length = inputParams.Length then
        contract inputArgs
        |> Result.bind(List.zip inputParams >> typecheckInputs >> contract)
    else
        Error [MismatchArgNum (pos, declName.ToString(), inputArgs.Length, inputParams.Length)]


/// Type check expressions that appear on the right hand side.
// AST.Literal does not comprise struct, array,... literals
let private checkSimpleLiteral literal =
    match literal with
    | AST.Bool (value = bc; range = pos) -> { rhs = BoolConst bc; typ = Types.ValueTypes BoolType; range = pos } |> Ok
    // -- numerical constants --
    | AST.Int (value, _, pos) -> 
        if MIN_INT64 <= value && value <= MAX_NAT64 then // Int literals allow an unary minus in attributes
            { rhs = IntConst value; typ = AnyInt value; range = pos } |> Ok
        else
            Error [NumberLargerThanAnyInt(pos, value.ToString())]
    | AST.Bits (bits, pos) ->
        let v = bits.value
        if MIN_BITS64 <= v && v <= MAX_BITS64 then // Bits literals are always >= 0                    
            { rhs = BitsConst bits; typ = AnyBits v; range = pos } |> Ok
        else
            Error [NumberLargerThanAnyInt(pos, v.ToString())]  // Todo: Change this error message, fjg. 30.01.20                
    | AST.Float (number, _, pos) ->
        let v = number.value
        if MIN_FLOAT64 <= v && v <= MAX_FLOAT64 then // Float literals allow an unary minus in attributes
            { rhs = FloatConst number; typ = AnyFloat v; range = pos } |> Ok
        else
            Error [NumberLargerThanAnyFloat(pos, string number)]
    | AST.String _ ->
        Error [UnsupportedFeature (literal.Range, "undefined, string literal")]


/// Given some {...} literal, evaluate its fields and construct an Any typed literal
let rec private checkAggregateLiteral lut al r =
    match al with
        // empty {} may be an empty array or struct const, both represented by ResetConst
        | AST.ResetFields -> Ok { rhs = ResetConst; typ = AnyComposite; range = r }
        // for every given struct field "ident=expr", check expr recursively
        | AST.StructFields fields ->
            fields
            |> List.map (fun field -> Ok field.name.id |> combine <| checkExpr lut field.expr)
            |> contract
            |> Result.map (fun typedFields -> { rhs = StructConst typedFields; typ = AnyComposite; range = r })
        // for every array field "[idx]=expr", 
        //  check expr recursively
        //  if idx is not given, then assign the next available index, starting from 0
        //  otherwise, check that 
        //      - idx evaluates to a non-negative integer constant
        //      - that number is at least as large as the running index counter,
        //        and update the index counter
        | AST.ArrayFields fields ->
            let ensureNonNeg pos num =
                if num >= 0 then Ok num
                else Error [NonNegIdxExpected(pos, num)]
            let checkIdx idx =
                checkExpr lut idx 
                |> Result.bind (evalCompTimeInt lut)
                |> Result.bind (ensureNonNeg idx.Range)
            // Check that indices, if there are any, are non-negative compile time constants
            // and in order and do not repeat.
            // Note that the exact array length is unknown at this point, nor do we know the
            // declared array type.
            let rec checkFields curIdx fs =
                match fs with
                | [] -> []
                | (field: AST.ArrayField) :: rest ->
                    match field.index with // determine which index this field has
                    | None -> Ok curIdx
                    | Some idx -> 
                        checkIdx idx
                        |> Result.bind (fun num -> 
                            if num >= curIdx then
                                Ok num
                            else
                                Error[ReInitArrayIndex(field.range, num, curIdx)]
                            )
                    |> function
                    | Ok thisFieldNum -> // field index determined successfully
                        (combine 
                        <| Ok thisFieldNum
                        <| checkExpr lut field.value) // yields a pair of index and typechecked value 
                        :: checkFields (thisFieldNum + 1) rest // continue with the next array index
                    | Error x -> [Error x] // in case of error, just wrap it in a list and stop recursion
            
            checkFields 0 fields
            |> contract
            |> Result.map (fun ckdFields -> { rhs = ArrayConst ckdFields; typ = AnyComposite; range = r})

/// Translate a dynamic access path to a typed memory location
and private checkUntimedDynamicAccessPath lut dname =
    let qname, subexpr = lut.ncEnv.decomposeDpath dname
    let tmlInit =
        combine 
        <| Ok (Loc qname) 
        <| (getTypeFromDecl lut qname dname.range)
    match subexpr with
    | [] ->
        tmlInit
    | accesses -> 
        let processAccessOn tmlAndType acc =
            match acc with
            | AST.Access.Name _ -> failwith "A subexpression cannot be a Name."
            | AST.Point (name,_) -> 
                // check whether tml has a field "name" and what type that is
                tmlAndType
                |> Result.bind (fun (tml,typ) ->
                    match typ with
                    | Types.ValueTypes (ValueTypes.StructType (_, typname, typfields))
                    | Types.ReferenceTypes (ReferenceTypes.StructType(_, typname, typfields)) ->
                        typfields
                        |> List.tryFind (fun f -> f.name.basicId = name.id)
                        |> function
                            | None -> Error [FieldNotAMember(name, tml)]
                            | Some varDecl -> Ok (tml.AddFieldAccess name.id, varDecl.datatype)
                    | _ -> Error [FieldAccessOnNonStructType(name, tml)]
                )
            | AST.Index (idx, r) ->
                let isIntType = function
                    | AnyInt _
                    | ValueTypes (IntType _)
                    | ValueTypes (NatType _) -> true
                    | _ -> false
                // check that tml is actually an array
                tmlAndType
                |> Result.bind (fun (tml,typ) -> // given a valid type
                    match typ with
                    | ValueTypes (ArrayType (asize, dty)) -> // ensure it is an array type
                        checkExpr lut idx
                        |> Result.bind (fun trhs -> // evaluate the index expression
                            if isIntType trhs.typ then // make sure it is an integer
                                match evalCompTimeInt lut trhs with // if it is constant we can even check boundaries
                                | Ok actualIndex ->
                                    if 0 <= actualIndex && actualIndex < asize then
                                        let constIdx = {rhs = IntConst (bigint actualIndex); typ = trhs.typ; range = trhs.range}
                                        Ok (tml.AddArrayAccess constIdx, ValueTypes dty)
                                    else
                                        Error [StaticArrayOutOfBounds(dname.Range, trhs, tml.AddArrayAccess trhs, asize - 1)] // -1 since we need the maximal index in the error message
                                | Error es -> // the index is determined at runtime
                                    if isConstVarDecl lut tml then // but then the array must not be constant
                                        ConstArrayRequiresConstIndex dname.Range :: es |> Error
                                    else // param/let/var array with dynamic access, Ok
                                        Ok (tml.AddArrayAccess trhs, ValueTypes dty)
                            else
                                Error [IndexMustBeInteger(dname.Range, trhs, tml.AddArrayAccess trhs)]
                            )
                    | _ -> Error [ArrayAccessOnNonArrayType(r, tml)]
                    )
            | AST.StaticIndex _ ->
                Error [UnsupportedFeature (acc.Range, "static array indices or optionals")]
        List.fold processAccessOn tmlInit accesses


/// Shorthand helper. Given two expressions e1, e2 and a combination 
/// function f (and, or, +, -, ...), type check e1 and e2 and combine
/// using f.
and private combineTwoExpr lut e1 e2 f =
    combine (checkExpr lut e1) (checkExpr lut e2)
    |> Result.bind f


/// Given an untyped AST.Expr, return a typed expression.
/// We guarantee that compile time expressions are evaluated to a literal
/// BoolConst, IntConst, FloatConst, ResetConst, StructConst, ArrayConst
/// where the latter two may only contain const literals in their fields recursively.
and internal checkExpr (lut: TypeCheckContext) expr: TyChecked<TypedRhs> =
    match expr with
    | AST.Expr.Const literal -> checkSimpleLiteral literal
    | AST.Expr.AggregateConst (ac, r) -> checkAggregateLiteral lut ac r
    | AST.Expr.SliceConst (_, _, _, r) -> Error [UnsupportedFeature (r, "slice const")] // TODO
    | AST.Expr.ImplicitMember spath -> Error [UnsupportedFeature (spath.Range, "implicit members")] // TODO
    // -- variables --
    | AST.Expr.Var dname ->
        let makeTimedRhsStructure ( tml, dty ) =
            match dname.timepoint with
            | AST.TemporalQualification.Current ->
                // while checkExpr tries to evaluate trivial expressions, it does NOT however substitute names for values in constants
                // this is the reason why there is a separate evalConst function that does exactly that
                Ok {rhs = RhsCur tml; typ = dty; range = dname.Range}
            | AST.TemporalQualification.Next r -> Error [NextOnRhs (r, dname.pathToString)]
            | AST.TemporalQualification.Previous _ ->
                // check that prev is used on a value typed, local variable
                match dty with
                | ValueTypes _ ->
                    let qname = tml.QNamePrefix
                    match lut.nameToDecl.[qname] with
                    | Declarable.VarDecl {mutability = m} //OK, local variable
                    | Declarable.ExternalVarDecl {mutability = m} -> 
                        match m with
                        // local var 
                        | Mutability.Variable ->
                            Ok {rhs = Prev tml; typ = dty; range = dname.Range}
                        | Mutability.Immutable | Mutability.StaticParameter | Mutability.CompileTimeConstant ->
                            Error [PrevOnImmutable(expr.Range, qname)]
                    | Declarable.ParamDecl _ -> //Error
                        Error [PrevOnParam(expr.Range, qname)]
                    | Declarable.SubProgramDecl _
                    | Declarable.FunctionPrototype _ -> failwith "QName prefix of a TML cannot point to a subprogram!"
                | ReferenceTypes _
                | AnyComposite 
                | AnyInt _
                | AnyBits _ 
                | AnyFloat _ -> Error [PrevOnlyOnValueTypes(expr.Range, dty)]
        checkUntimedDynamicAccessPath lut dname
        |> Result.bind makeTimedRhsStructure
    // -- function call --
    | AST.FunctionCall (fp, readArgs, writeArgs, r) ->
        let resIn = List.map (checkExpr lut) readArgs
        let resOut = List.map (checkLExpr lut) writeArgs
        checkFunCall false lut r fp resIn resOut
        |> Result.bind(fun (f, t) -> {rhs = RhsStructure.FunCall f; typ = Types.ValueTypes t; range = r} |> Ok)
    // -- logical and bitwise not --
    | AST.Not (subexpr, r) ->
        checkExpr lut subexpr
        |> Result.bind (negate r)
    // -- logical operators
    | AST.And (e1, e2) -> combineTwoExpr lut e1 e2 formConjunction
    | AST.Or (e1, e2) -> combineTwoExpr lut e1 e2 formDisjunction    
    // -- numerical operations --
    | AST.Add (e1, e2) -> combineTwoExpr lut e1 e2 addition
    | AST.Sub (e1, e2) -> combineTwoExpr lut e1 e2 subtraction
    | AST.Mul (e1, e2) -> combineTwoExpr lut e1 e2 product
    | AST.Div (e1, e2) -> combineTwoExpr lut e1 e2 quotient
    | AST.Mod (e1, e2) -> combineTwoExpr lut e1 e2 remainder
    | AST.Pow _ -> Error [UnsupportedFeature (expr.Range, "exponentiation")] // TODO
    | AST.Unm (e, r) -> 
        // since we use AnyInt for literals without a size, it is fine to
        // first check the literal recursively and then apply unaryMinus
        checkExpr lut e
        |> Result.bind (unaryMinus r)

    // --- relational operators

    //| AST.Eq (e1, e2) -> 
    //    // can be applied to logical, numerical and structured data, yields logical value
    //    let te1 = checkExpr lut e1 |> Result.map (tryEvalConst lut)
    //    let te2 = checkExpr lut e2 |> Result.map (tryEvalConst lut)
    //    combine te1 te2
    //    |> Result.bind formEquality

    | AST.Eq (e1, e2) -> combineTwoExpr lut e1 e2 equal
    | AST.Ieq (e1, e2) -> checkExpr lut (AST.Not(AST.Eq(e1, e2), Range.unionRanges e1.Range e2.Range))
    | AST.Les (e1, e2) -> combineTwoExpr lut e1 e2 lessThan
    | AST.Leq (e1, e2) -> combineTwoExpr lut e1 e2 lessEqualThan
    | AST.Grt (e1, e2) -> checkExpr lut (AST.Les(e2, e1))
    | AST.Geq (e1, e2) -> checkExpr lut (AST.Leq(e2, e1))
    
    
    // -- bitwise operators, TODO: complete this, fjg. 21.01.20
    | AST.Bnot (subexpr, r) ->
        checkExpr lut subexpr
        |> Result.bind (negate r)
    | AST.Bor (e1, e2) -> combineTwoExpr lut e1 e2 formDisjunction
    | AST.Band (e1, e2) -> combineTwoExpr lut e1 e2 formConjunction
    | AST.Bxor (e1, e2) -> combineTwoExpr lut e1 e2 formXor
    | AST.Shl _
    | AST.Shr _  
    
    // -- Advance bitwise operators
    | AST.Sshr _
    | AST.Rotl _
    | AST.Rotr _ -> //TODO
        Error [UnsupportedFeature (expr.Range, "advanced bitwise operator: '+>>' or '<<>'  or '<>>'")]
    // --- identity operators
    | AST.Ideq _ 
    | AST.Idieq _ ->
        Error [UnsupportedFeature (expr.Range, "identity operator")]
    // -- type conversions --
    | AST.Convert (e, t) -> // convert a given expression into a given type, e.g. "sensors[1].speed as float32[mph]"
        Error [UnsupportedFeature (expr.Range, "type conversion")]
    // -- type annotation --
    | AST.HasType (e, t) -> // determines the type of a literal, e.g. 42: bits8, are is an alternative for e.g. var x = expr: type
        let rhs = checkExpr lut e
        let lty = checkDataType lut t
        combine rhs lty
        |> Result.bind (fun (rhs, lty) -> amendRhsExpr false lty rhs)  //TODO: refactor amendRhsExpr
    // -- operators on arrays and slices --
    | AST.Len _
    | AST.Cap _ -> //TODO
        Error [UnsupportedFeature (expr.Range, "length or capacity")]
    // -- parentheses --
    | AST.Expr.Parens (expr, _) ->
        checkExpr lut expr
        |> Result.map (fun e -> e.SetRange expr.Range)

/// Given an untyped datatype, return a type checked datatype .
and internal checkDataType lut utyDataType =
    match utyDataType with
    // simple types
    | AST.BoolType _ -> ValueTypes BoolType |> Ok
    | AST.IntegerType (size, _, _) -> IntType size |> ValueTypes |> Ok
    | AST.NaturalType (size, _, _) -> NatType size |> ValueTypes |> Ok
    | AST.BitvecType (size, _) -> BitsType size |> ValueTypes |> Ok
    | AST.FloatType (size, _, _) -> FloatType size |> ValueTypes |> Ok
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
            checkDataType lut elemDty
            |> Result.bind(fun dty -> 
                match dty with
                | ValueTypes sth ->
                    ArrayType (checkedSize, sth)
                    |> ValueTypes
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
    | AST.SliceType _
    | AST.Signal _ -> 
        Error [UnsupportedFeature (utyDataType.Range, "types other than bool, int, nat, float, fixed size array or user defined struct")]


/// Type check expressions that appear on the left hand side.
and internal checkLExpr lut (dname: AST.DynamicAccessPath) =
    let makeTimedLhsStructure ( tml, dty ) =
        match dname.timepoint with
        | AST.TemporalQualification.Current -> Ok {lhs = LhsCur tml; typ = dty; range = dname.Range}
        | AST.TemporalQualification.Previous r -> Error [PrevOnLhs (r, dname.pathToString)]
        | AST.TemporalQualification.Next _ ->  Ok {lhs = LhsNext tml; typ = dty; range = dname.Range}
    checkUntimedDynamicAccessPath lut dname
    |> Result.bind makeTimedLhsStructure


and internal checkAssignLExpr lut lhs =
    match lhs with
    | AST.Wildcard _ -> Ok { lhs = Wildcard; typ = AnyComposite; range = lhs.Range }
    | AST.Loc dname
    | AST.EventLoc dname ->
        checkLExpr lut dname


/// Type check functions calls.
/// A function call can either appear as a statement and then must call a void function.
/// Or a function call can be part of an expression and then the called function must return a non-void, first class value.
and internal checkFunCall isStatement (lut: TypeCheckContext) pos (fp: AST.Code) (inputs: Result<_,_> list) (outputs: Result<_,_> list) =
    let checkIsFunction decl =
        if decl.isFunction then Ok()
        else Error [FunCallToAct(pos, decl)]

    let checkReturnType declName declReturns =
        if isStatement then
            match declReturns with
            | Void -> Ok ()
            | _ -> Error [CannotCallNonVoidFunAsStmt (pos, declName)]
        else
            match declReturns with
            | Void -> Error [FunCallInExprMustBeNonVoid (pos, declName)]
            | _ -> Ok ()
    
    let createCall (name, typ) (((_, ins), outs), _) =
        (name, ins, outs), typ

    match fp with
    | AST.Procedure dname ->
        ensureCurrent dname
        |> Result.map lut.ncEnv.dpathToQname
        |> Result.bind (getSubProgDeclAsPrototype lut pos)
        |> Result.bind (fun decl ->
            checkIsFunction decl
            |> combine <| checkInputs pos inputs decl.name decl.inputs
            |> combine <| checkOutputs lut pos outputs decl.name decl.outputs
            |> combine <| checkReturnType decl.name decl.returns
            |> Result.map (createCall (decl.name, decl.returns))
            )


/// Type check activity calls.
/// An activity may return a value that is stored in resStorage upon termination.
/// This is different to a function call which 
let internal checkActCall lut pos (ap: AST.Code) resStorage (inputs: Result<_,_> list) outputs =
    let checkIsActivity decl =
        if not decl.isFunction then Ok()
        else Error [RunAFun(pos, decl)]
    let checkReturnType storage declName declReturns =
        match storage with
        | None ->
            match declReturns with
            | Void -> Ok None
            | _ -> Error [ActCallMustExplicitlyIgnoreResult (pos, declName.basicId)]
        | Some leftExprRes ->
            leftExprRes |> Result.bind (
                fun lexpr -> 
                    match lexpr.typ with 
                    | Types.AnyComposite when lexpr.lhs = Wildcard ->
                        Ok None
                    | Types.ValueTypes _ ->
                        Ok (Some lexpr) 
                    | _ -> Error [ ValueMustBeOfValueType (lexpr) ]
                )
        |> Result.bind (
            function
            | None -> Ok None
            | Some (lexpr: TypedLhs) ->
                let typ = lexpr.typ
                if isLhsMutable lut lexpr.lhs then
                    if isLeftSupertypeOfRight typ (Types.ValueTypes declReturns) then 
                        Ok (Some lexpr) 
                    else 
                        Error [ReturnTypeMismatch(pos, declReturns, typ)]
                else Error [AssignmentToImmutable (pos, lexpr.ToString())]
                )
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
            |> combine <| checkReturnType resStorage decl.name decl.returns
            |> Result.map (createCall decl.name)
            )

/// Check that condition is a boolean, side-effect free expression
let internal fCondition lut cond = 
    let ensureBoolean (e: TypedRhs) =
        match e.typ with
        | Types.ValueTypes BoolType -> Ok e
        | _ -> Error [ExpectedBoolCond (e.Range, e)]
    let ensureSideEffectFree (e: TypedRhs) =
        if hasNoSideEffect e then Ok e
        else Error [ConditionHasSideEffect e]
    match cond with
    | AST.Cond expr ->
        checkExpr lut expr
        |> Result.bind ensureBoolean
        |> Result.bind ensureSideEffectFree
        |> Result.map (tryEvalConst lut)
    | AST.SignalBinding _ -> Error [UnsupportedFeature (cond.Range, "optional binding")]
    | AST.Tick _ -> Error [UnsupportedFeature (cond.Range, "tick condition")]


/// Unsafe negation, we assume structure has boolean type. This must be 
/// ensured by the caller.
let public unsafeNeg = neg

/// Unsafe conjunction, we assume arguments have boolean type. This must be 
/// ensured by the caller.
let public unsafeConj = conj