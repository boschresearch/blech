﻿// Copyright (c) 2019 - for information on the respective copyright owner
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

open Constants
open CommonTypes
open BlechTypes
open TyChecked
open Evaluation
open TypeCheckContext
open TyChkAmendment


//=========================================================================
// Functions for checking type and expression properties
//=========================================================================

let internal ensureCurrent (dname: AST.DynamicAccessPath) =
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
            | Declarable.ProcedureImpl _
            | Declarable.ProcedurePrototype _ ->
                failwith "Asking for mutability of a subprogram. That cannot be right."
        else
            failwith <| sprintf "Lhs %s not in nameToDecl" (qname.ToString())
    | FieldAccess (tml, ident) ->
        let ism, typ = isTmlMutable tml
        if ism then
            match typ with
            | ValueTypes (ValueTypes.StructType (typname, typfields))
            | ReferenceTypes (ReferenceTypes.StructType(_, typname, typfields)) ->
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
    | ReturnVar -> true
    | LhsCur tml
    | LhsNext tml -> fst <| isTmlMutable tml


/// Returns true when the evaluation of expr does not change the program's state
let rec private hasNoSideEffect lut expr =
    let recHasNoSideEffect = hasNoSideEffect lut
    let recurFields fields =
        fields
        |> List.map (snd >> recHasNoSideEffect)
        |> List.forall id
    match expr.rhs with
    // locations
    | RhsCur tml 
    | Prev tml -> tml.FindAllIndexExpr |> List.forall recHasNoSideEffect
    // constants and literals
    | BoolConst _ | IntConst _ | BitsConst _ | NatConst _ | FloatConst _  | ResetConst -> true
    | StructConst fields -> recurFields fields
    | ArrayConst elems -> recurFields elems
    // call, has no side-effect if it does not write any outputs, 
    // nor changes anything in the environment (singleton!)
    // this assumption is only valid when there are not global variables (as is the case in Blech)
    | FunCall (qname, inputs, outputs) ->
        let isSingleton =
            lut.nameToDecl.[qname].TryGetPrototype
            |> function
                | None -> false
                | Some prot -> prot.IsSingleton
        List.isEmpty outputs 
        && not isSingleton
        && List.forall recHasNoSideEffect inputs
    // type conversion
    | Convert (e, _, _) -> recHasNoSideEffect e
    // unary 
    | Neg e | Bnot e -> recHasNoSideEffect e
    // logical
    | Conj (x, y) | Disj (x, y) 
    // bitwise 
    | Band (x, y) | Bor (x, y) | Bxor (x, y)
    | Shl (x, y) | Shr (x, y) | Sshr (x, y) | Rotl (x, y) | Rotr (x, y)
    // relational
    | Les (x, y) | Leq (x, y) | Equ (x, y)
    // arithmetic
    | Add (x, y) | Sub (x, y) | Mul (x, y) | Div (x, y) | Mod (x, y) -> 
        recHasNoSideEffect x && recHasNoSideEffect y


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
    | BoolConst _ | IntConst _ | BitsConst _ | FloatConst _ | NatConst _ | ResetConst -> true
    | StructConst fields -> recurFields fields
    | ArrayConst elems -> recurFields elems
    | FunCall _ -> false // we do not have compile time functions yet
    // type conversion 
    | Convert (e, _, _) -> isStaticExpr lut e
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
    | IntConst a, IntConst b -> IntConst <| Arithmetic.Add (a, b)
    | NatConst a, NatConst b -> NatConst <| Arithmetic.Add (a, b)
    | BitsConst a, BitsConst b -> BitsConst <| Arithmetic.Add (a, b)
    | FloatConst a, FloatConst b -> FloatConst <| Arithmetic.Add (a, b)
    | _ -> Add(this, that)

let private mul this that =
    match this.rhs, that.rhs with
    | IntConst a, IntConst b -> IntConst <| Arithmetic.Mul (a, b)
    | NatConst a, NatConst b -> NatConst <| Arithmetic.Mul (a, b)
    | BitsConst a, BitsConst b -> BitsConst <| Arithmetic.Mul (a, b)
    | FloatConst a, FloatConst b -> FloatConst <| Arithmetic.Mul (a, b)
    | _ -> Mul(this, that)

let private div this that =    
    match this.rhs, that.rhs with
    | IntConst a, IntConst b -> IntConst <| Arithmetic.Div (a, b)
    | NatConst a, NatConst b -> NatConst <| Arithmetic.Div (a, b)
    | BitsConst a, BitsConst b -> BitsConst <| Arithmetic.Div (a, b)
    | FloatConst a, FloatConst b -> FloatConst <| Arithmetic.Div (a, b)
    | _ -> Div(this, that)

let private sub this that =
    match this.rhs, that.rhs with
    | IntConst a, IntConst b -> IntConst <| Arithmetic.Sub (a, b)
    | NatConst a, NatConst b -> NatConst <| Arithmetic.Sub (a, b)
    | BitsConst a, BitsConst b -> BitsConst <| Arithmetic.Sub (a, b)
    | FloatConst a, FloatConst b -> FloatConst <| Arithmetic.Sub (a, b)
    | _ -> Sub(this, that)

let private modus this that =
    match this.rhs, that.rhs with
    | IntConst a, IntConst b -> IntConst <| Arithmetic.Mod (a, b)
    | NatConst a, NatConst b -> NatConst <| Arithmetic.Mod (a, b)
    | BitsConst a, BitsConst b -> BitsConst <| Arithmetic.Mod (a, b)
    // | FloatConst a, FloatConst b -> failwith "modulo operation on float should not occur" // this is checked before calling this function 
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

let private less this that =
    match this.rhs, that.rhs with
    | BoolConst a, BoolConst b -> BoolConst (a < b)
    | IntConst a, IntConst b -> BoolConst <| Relational.Lt (a, b)
    | BitsConst a, BitsConst b -> BoolConst <| Relational.Lt (a, b)
    | FloatConst a, FloatConst b -> BoolConst <| Relational.Lt (a, b)
    | _ -> Les(this, that)

let private leq this that =
    match this.rhs, that.rhs with
    | BoolConst a, BoolConst b -> BoolConst ( a <= b )
    | IntConst a, IntConst b -> BoolConst <| Relational.Le (a, b)
    | BitsConst a, BitsConst b -> BoolConst <| Relational.Le (a, b)
    | FloatConst a, FloatConst b -> BoolConst <| Relational.Le (a, b)
    | _ -> Leq(this, that)

let private eq this that =
    match this.rhs, that.rhs with
    | BoolConst a, BoolConst b -> BoolConst (a = b)
    | IntConst a, IntConst b -> BoolConst <| Relational.Eq (a, b)
    | BitsConst a, BitsConst b -> BoolConst <| Relational.Eq (a, b)
    | FloatConst a, FloatConst b -> BoolConst <| Relational.Eq (a, b)
    | _ -> Equ(this, that)

let private bnot this = 
    match this.rhs with
    | BitsConst b -> BitsConst <| Bitwise.Bnot b
    | _ -> Bnot this

let private bor this that =
    match this.rhs, that.rhs with
    | BitsConst a, BitsConst b -> BitsConst <| Bitwise.Bor (a, b)
    | _ -> Bor(this, that)

let private band this that =
    match this.rhs, that.rhs with
    | BitsConst a, BitsConst b -> BitsConst <| Bitwise.Band (a, b)
    | _ -> Band (this, that)

let private bxor this that =
    match this.rhs, that.rhs with
    | BitsConst a, BitsConst b -> BitsConst <| Bitwise.Bxor (a, b)
    | _ -> Bxor (this, that)

let private shl expr amount = 
    match expr.rhs, amount.rhs with
    | BitsConst bs, IntConst i -> BitsConst <| Bitwise.Shl (bs, i.GetShiftAmount bs.getBitsize)
    | BitsConst bs, NatConst n -> BitsConst <| Bitwise.Shl (bs, n.GetShiftAmount bs.getBitsize)
    | BitsConst bs, BitsConst b -> BitsConst <| Bitwise.Shl (bs, b.GetShiftAmount bs.getBitsize)
    | _ -> Shl (expr, amount)

let private shr expr amount = 
    match expr.rhs, amount.rhs with
    | BitsConst bs, IntConst i -> BitsConst <| Bitwise.Shr (bs, i.GetShiftAmount bs.getBitsize)
    | BitsConst bs, NatConst n -> BitsConst <| Bitwise.Shr (bs, n.GetShiftAmount bs.getBitsize)
    | BitsConst bs, BitsConst b -> BitsConst <| Bitwise.Shr (bs, b.GetShiftAmount bs.getBitsize)
    | _ -> Shr (expr, amount)


let private sshr expr amount = 
    match expr.rhs, amount.rhs with
    | BitsConst bs, IntConst i -> BitsConst <| Bitwise.Sshr (bs, i.GetShiftAmount bs.getBitsize)
    | BitsConst bs, NatConst n -> BitsConst <| Bitwise.Sshr (bs, n.GetShiftAmount bs.getBitsize)
    | BitsConst bs, BitsConst b -> BitsConst <| Bitwise.Sshr (bs, b.GetShiftAmount bs.getBitsize)
    | _ -> Sshr (expr, amount)


let private rotl expr amount = 
    match expr.rhs, amount.rhs with
    | BitsConst bs, IntConst i -> BitsConst <| Bitwise.Rotl (bs, i.GetShiftAmount bs.getBitsize)
    | BitsConst bs, NatConst n -> BitsConst <| Bitwise.Rotl (bs, n.GetShiftAmount bs.getBitsize)
    | BitsConst bs, BitsConst b -> BitsConst <| Bitwise.Rotl (bs, b.GetShiftAmount bs.getBitsize)
    | _ -> Rotl (expr, amount)


let private rotr expr amount = 
    match expr.rhs, amount.rhs with
    | BitsConst bs, IntConst i -> BitsConst <| Bitwise.Rotr (bs, i.GetShiftAmount bs.getBitsize)
    | BitsConst bs, NatConst n -> BitsConst <| Bitwise.Rotr (bs, n.GetShiftAmount bs.getBitsize)
    | BitsConst bs, BitsConst b -> BitsConst <| Bitwise.Rotr (bs, b.GetShiftAmount bs.getBitsize)
    | _ -> Rotr (expr, amount)


// let private convert toType behaviour expr =
//     match expr.rhs, toType with
//     | IntConst i, ValueTypes (IntType it) -> IntConst <| Conversion.IntToInt (i, it)
//     | IntConst i, ValueTypes (NatType nt) -> NatConst <| Conversion.IntToNat (i, nt)
//     | IntConst i, ValueTypes (BitsType bt) -> BitsConst <| Conversion.IntToBits (i, bt)
//     | IntConst i, ValueTypes (FloatType ft) -> FloatConst <| Conversion.IntToFloat (i, ft)
//     | NatConst n, ValueTypes (NatType nt) -> NatConst <| Conversion.NatToNat (n, nt)
//     | NatConst n, ValueTypes (IntType it) -> IntConst <| Conversion.NatToInt (n, it)
//     | NatConst n, ValueTypes (BitsType bt) -> BitsConst <| Conversion.NatToBits (n, bt)
//     | NatConst n, ValueTypes (FloatType ft) -> FloatConst <| Conversion.NatToFloat (n, ft)
//     | BitsConst b, ValueTypes (BitsType bt) -> BitsConst <| Conversion.BitsToBits (b, bt)
//     | BitsConst b, ValueTypes (IntType it) -> IntConst <| Conversion.BitsToInt (b, it)
//     | BitsConst b, ValueTypes (NatType nt) -> NatConst <| Conversion.BitsToNat (b, nt)
//     | BitsConst b, ValueTypes (FloatType ft) -> FloatConst <| Conversion.BitsToFloat (b, ft)
//     | FloatConst f, ValueTypes (FloatType ft) -> FloatConst <| Conversion.FloatToFloat (f, ft)
//     | _ -> Convert (expr, toType, behaviour)   

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
    let evalUnary x f = 
        let newRhs = tryEvalConst lut x |> f
        { rhs = newRhs; typ = checkedExpr.typ; range = checkedExpr.Range }
    
    let evalBin x y f =
        let newrhs = tryEvalConst lut x |> f <| tryEvalConst lut y
        { rhs = newrhs; typ = checkedExpr.typ; range = checkedExpr.Range }
    
    let recurFields constBuilder fs =
        let kvps = fs |> List.map (fun (i,f) -> i, tryEvalConst lut f)
        { rhs = constBuilder kvps
          typ = checkedExpr.typ
          range = checkedExpr.Range }
    
    match checkedExpr.rhs with
    // simple literal
    | IntConst _ | BoolConst _ | BitsConst _ | NatConst _ | FloatConst _ | ResetConst -> checkedExpr
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
    | Bnot x  -> evalUnary x bnot 
    | Neg x -> evalUnary x neg
    // logical
    | Conj (x, y) -> evalBin x y conj
    | Disj (x, y) -> evalBin x y disj
    // bitwise
    | Band (x, y) -> evalBin x y band
    | Bor (x, y) -> evalBin x y bor
    | Bxor (x, y) -> evalBin x y bxor 
    | Shl (x, y) -> evalBin x y shl
    | Shr (x, y) -> evalBin x y shr
    | Sshr (x, y) -> evalBin x y sshr
    | Rotl (x, y) -> evalBin x y rotl
    | Rotr (x, y) -> evalBin x y rotr
    // relational
    | Les (x, y) -> evalBin x y less 
    | Leq (x, y) -> evalBin x y leq
    | Equ (x, y) -> evalBin x y eq 
    // type conversion
    // | Convert (x, t, b) -> evalUnary x (convert t b)  // Todo move constant conversion completely to typechecking, schorg 27.03.20
    | Convert (x, t, b) -> // Possible evaluations already done during typecheck 
        { checkedExpr with rhs = Convert(tryEvalConst lut x, t, b) }
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
                | Ok trhs -> { trhs with range = checkedExpr.Range }// is constant by definition
                | Error _ -> checkedExpr // the tml access fails for arr[foo], where foo is not a compile time const
            else
                checkedExpr
        //| Declarable.ParamDecl _ -> Error [] // params are not compile time const
        | _ -> checkedExpr


/// This tries to evaluate expr to a constant value
/// and returns a MustBeConst error if this operation fails.
and internal evalConst lut expr =
    let res = tryEvalConst lut expr
    if isConstantExpr lut res then Ok res
    else Error[MustBeConst(expr)]



and private ensureNonNegIndex index =
    match index.rhs with
    | IntConst i when i.IsNegative ->
        Error [ NegativeArrayIndex index ]
    | _ ->
        Ok index
    
and private ensurePositiveSize index = 
    match index.rhs with
    | IntConst i when not i.IsPositive ->
        Error [ PositiveSizeExpected index ]
    | NatConst n when not n.IsPositive ->
        Error [ PositiveSizeExpected index ]
    | BitsConst b when not b.IsPositive ->
        Error [ PositiveSizeExpected index ]
    | _ ->
        Ok index


and private ensureArraySize wordsize index =
    match index.rhs with
    | IntConst i when not (i.IsSize wordsize) ->
        Error [ ArraySizeOverflowsWordsize (index, wordsize) ] 
    | NatConst n when not (n.IsSize wordsize) ->
        Error [ ArraySizeOverflowsWordsize (index, wordsize) ] 
    | BitsConst b when not (b.IsSize wordsize) ->
        Error [ ArraySizeOverflowsWordsize (index, wordsize) ] 
    | _ ->
        Ok index


/// This evaluate expr to a constant array size
and internal evalCompTimeSize lut expr =   
    evalConst lut expr
    |> Result.bind ensurePositiveSize
    |> Result.bind (ensureArraySize lut.cliContext.wordSize) // A size must be >= 0 before it can be extracted with .GetArrayIndex
    |> Result.bind (fun constExpr ->
        match constExpr.rhs with
        | IntConst i -> Ok i.GetArrayIndex
        | NatConst n -> Ok n.GetArrayIndex
        | BitsConst b -> Ok b.GetArrayIndex
        | _ -> 
            Error [NotACompileTimeSize expr]    
    )

/// This evaluate expr to a constant array index.
/// It retruns the compile time index.
/// It returns an error if the compile time index is negative or overflows the wordsize.
and internal evalCompTimeIndex lut expr =   
    evalConst lut expr
    |> Result.bind ensureNonNegIndex
    |> Result.bind (ensureArraySize lut.cliContext.wordSize) // A size must be >= 0 before it can be extracted with .GetArrayIndex
    |> Result.bind (fun constExpr ->
        match constExpr.rhs with
        | IntConst i -> Ok i.GetArrayIndex
        | NatConst n -> Ok n.GetArrayIndex
        | BitsConst b -> Ok b.GetArrayIndex
        | _ -> 
            Error [NotACompileTimeSize expr]    
    )


/// This tries to evaluate an index expr to a constant value.
/// It returns the optional compile time index,
/// and an error is the constant value is negative
and internal tryEvalCompTimeIndex lut expr =
    tryEvalConst lut expr 
    |> ensureNonNegIndex
    |> Result.bind (fun expr ->
        match expr.rhs with
        | IntConst i -> Ok <| Some i.GetArrayIndex
        | NatConst n -> Ok <| Some n.GetArrayIndex
        | BitsConst b -> Ok <| Some b.GetArrayIndex
        | _ -> Ok None        
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
                        | ValueTypes (ValueTypes.StructType (_, fields)) ->
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
                evalCompTimeIndex lut idx
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

// ------------------------------------------------------------------------
// ---  Unary operators, 
// ---  logical negate 'not', bitwise complement '~' and unary minus '-'
// ------------------------------------------------------------------------

/// Given a typed expression, construct its negation.
/// If the type is not boolean, an error will be returned instead.
let private negate rng (expr: TypedRhs) =
    match expr.typ with
    | ValueTypes BoolType ->
        Ok { expr with rhs = neg expr }
    | _ -> Error [ExpectedBoolExpr (rng, expr)]

/// Given a typed expression, construct its bitwise complement
/// If the the type is not BitsType, an error will returned instead
let private complement rng (expr: TypedRhs) =
    match expr.typ with
    | ValueTypes (BitsType size) ->
        Ok { expr with rhs = bnot expr }
    | AnyBits ->
        Error [ComplementOnAnyBits (rng, expr)]
    | _ -> Error [ExpectedBitsExpr (rng, expr)]

/// Unsafe unaryMinus, we assume structure has arithmetic type. This must be
/// ensured by the caller.
let private unsafeUnaryMinus (expr: TypedRhs) = 
    match expr.typ with
    | ValueTypes (IntType size) ->
        match expr.rhs with
        | IntConst i -> IntConst <| Arithmetic.Unm i
        | _ -> Sub ({expr with rhs = IntConst <| Constant.Zero size }, expr) //0 - expr
    | ValueTypes (BitsType size) ->
        match expr.rhs with
        | BitsConst b -> BitsConst <| Arithmetic.Unm b
        | _ -> Sub ({expr with rhs = BitsConst <| Constant.Zero size }, expr) //0 - expr        
    | ValueTypes (FloatType size) ->
        match expr.rhs with
        | FloatConst f -> FloatConst <| Arithmetic.Unm f
        | _ -> Sub ( {expr with rhs = FloatConst <| Constant.Zero size}, expr) //0 - expr
    | AnyInt ->
        match expr.rhs with
        | IntConst i -> IntConst <| Arithmetic.Unm i
        | _ -> failwith "AnyInt should be always an IntConst"
    | AnyFloat ->
        match expr.rhs with
        | FloatConst f -> FloatConst <| Arithmetic.Unm f
        | _ -> failwith "AnyFloat should be always a FloatConst"
    | AnyBits -> 
        failwith "No unary minus on AnyBits literals"
    | _ -> 
        failwith "UnsafeUnaryMinus called with something other than Int, Bits or Float!"
    

/// Given a typed Expression, construct its negative.
/// If the type is not numeric, an error will be returned instead.
let private unaryMinus r (expr: TypedRhs) =
    try
        match expr.typ with
        // no unary minus on natural number since it cannot be used anywhere
        | ValueTypes (IntType _)
        | ValueTypes (BitsType _)
        | ValueTypes (FloatType _)
        | AnyInt
        | AnyFloat ->
            Ok { expr with range = r; rhs = unsafeUnaryMinus expr }
        | ValueTypes (NatType _) ->
            Error [UnaryMinusOnNatExpr (r, expr)]
        | AnyBits ->
            Error [UnaryMinusOnAnyBits (r, expr)]
        | _ ->
            Error [ExpectedInvertableNumberExpr (r, expr)]

    with
     | :? System.OverflowException -> 
         Error [UnaryMinusOverFlow (r, expr)]

// --------------------------------------------------------------------
// ---  Logical Operators
// --------------------------------------------------------------------

/// Given two typed expressions, construct their binary logical operator.
/// If some of the types is not boolean, an error will be returned instead.
let private formLogical operator ((expr1: TypedRhs), (expr2: TypedRhs)) =
    match expr1.typ, expr2.typ with
    | ValueTypes BoolType, ValueTypes BoolType ->
        let structure = operator expr1 expr2
        { rhs = structure; 
          typ = ValueTypes BoolType
          range = Range.unionRanges expr1.Range expr2.Range }
        |> Ok
    | _ -> Error [ExpectedBoolConds (expr1, expr2)]
    
/// Given two typed expressions, construct their conjunction.
/// If some of the types is not boolean, an error will be returned instead.
let private formConjunction = formLogical conj

/// Given two typed expressions, construct their disjunction.
/// If some of the types is not boolean, an error will be returned instead.
let private formDisjunction = formLogical disj


// --------------------------------------------------------------------
// ---  Bitwise binary operators
// --------------------------------------------------------------------

/// Given two typed expressions, construct their binary bitwise operator
/// If the two types are not comparable, an error will be returned instead.
let private combineBitwiseOp op ((expr1: TypedRhs), (expr2: TypedRhs)) =
    let rng = Range.unionRanges expr1.Range expr2.Range
    // let commonSize size1 size2 = if size1 >= size2 then size1 else size2 
    match expr1.typ, expr2.typ with    
    | ValueTypes (BitsType size1), ValueTypes (BitsType size2) when size1 = size2->
        Ok { rhs = op expr1 expr2; typ = ValueTypes (BitsType size1); range = rng }
    | ValueTypes (BitsType _), ValueTypes (BitsType _) -> // when size1 != size2
        Error [BitsTypesOfDifferentSize (rng, expr1, expr2)]
    | AnyBits, AnyBits ->
        Error [BitwiseOperationOnAnyBits (rng, expr1, expr2)]
    | _, _ ->
        Error [BitsTypesRequired (rng, expr1, expr2)] 


let private checkBitwise operator (expr1: TypedRhs) (expr2: TypedRhs) =
    let e1 = tryAmendPrimitiveAny expr2.typ expr1
    let e2 = tryAmendPrimitiveAny expr1.typ expr2

    combine e1 e2
    |> Result.bind (combineBitwiseOp operator)

/// Returns the bitwise or of two typed expressions or an error in case of type mismatch.
let private bitwiseOr ((expr1: TypedRhs), (expr2: TypedRhs)) = checkBitwise bor expr1 expr2

/// Returns the bitwise and of two typed expressions or an error in case of type mismatch.
let private bitwiseAnd ((expr1: TypedRhs), (expr2: TypedRhs)) = checkBitwise band expr1 expr2

/// Returns the bitwise xor of two typed expressions or an error in case of type mismatch.
let private bitwiseXor ((expr1: TypedRhs), (expr2: TypedRhs)) = checkBitwise bxor expr1 expr2

// --------------------------------------------------------------------
// ---  Bitwise shift operators
// --------------------------------------------------------------------

let private ensureShiftAmount bitsize num  =
    match num.rhs with
    | IntConst i when i.IsNegative ->
        Error [ NegativeShiftAmount num ] 
    | _ ->
        Ok num

/// This tries to evaluate expr to a constant shift amount
/// It returns the optional compile time size 
/// and returns a NonNegIdxExpected if the result is a negative compile time Size value
let internal tryEvalCompShiftAmount lut bitsize expr =
    tryEvalConst lut expr 
    |> ensureShiftAmount bitsize
    

/// Given two typed expressions, construct their binary bitwise operator
/// If the two types are not comparable, an error will be returned instead.
let private combineShiftOp shift ((expr: TypedRhs), (amount: TypedRhs)) =
    let rng = Range.unionRanges expr.Range amount.Range
    let rhs = shift expr amount
    Ok { expr with rhs = rhs; range = rng }
    

let private checkShiftOp lut shift (expr: TypedRhs) (amount: TypedRhs) =
    let rng = Range.unionRanges expr.range amount.range
    match expr.typ with
    | ValueTypes (BitsType bt) ->
        match amount.typ with
        | ValueTypes (IntType _)
        | ValueTypes (NatType _)
        | ValueTypes (BitsType _)
        | AnyInt
        | AnyBits ->
            tryEvalCompShiftAmount lut bt.GetSize amount
            |> combine (Ok expr)
            |> Result.bind (combineShiftOp shift)
        | _ ->
            Error [ NoShiftAmountType amount ] 
    
    | AnyBits -> 
        Error [ ShiftOperationOnAnyBits (rng, expr) ] 
    | _ ->
        Error [ ExpectedBitsExpr (rng, expr) ] 
            

/// Returns the right shift '>>' of a typed expression and a typed shift amount, or an error in case of type mismatch.
let private shiftRight lut ((expr: TypedRhs), (amount: TypedRhs)) = checkShiftOp lut shr expr amount

/// Returns the left shift '<<' of a typed expression and a typed shift amount, or an error in case of type mismatch.
let private shiftLeft lut ((expr: TypedRhs), (amount: TypedRhs)) = checkShiftOp lut shl expr amount

/// Returns the signed right shift '+>>' of a typed expression and a typed shift amount, or an error in case of type mismatch.
let private signedShiftRight lut ((expr: TypedRhs), (amount: TypedRhs)) = checkShiftOp lut sshr expr amount

/// Returns the left rotation '<<>' of a typed expression and a typed shift amount, or an error in case of type mismatch.
let private rotateLeft lut ((expr: TypedRhs), (amount: TypedRhs)) = checkShiftOp lut rotl expr amount

/// Returns the signed right rotation '<>>' of a typed expression and a typed shift amount, or an error in case of type mismatch.
let private rotateRight lut ((expr: TypedRhs), (amount: TypedRhs)) = checkShiftOp lut rotr expr amount


// --------------------------------------------------------------------
// ---  Relational Operators
// --------------------------------------------------------------------

/// Given two typed expressions, construct their relation.
/// We assume that operator is either 'less', 'leq', or 'eq' from above.
/// If the two types are not comparable, an error will be returned instead.
let private combineRelationalOp operator ((expr1: TypedRhs), (expr2: TypedRhs)) =
    let rng = Range.unionRanges expr1.range expr2.range
    match expr1.typ, expr2.typ with    
    | ValueTypes BoolType, ValueTypes BoolType
    | ValueTypes (IntType _), ValueTypes (IntType _)
    | ValueTypes (NatType _), ValueTypes (NatType _)
    | ValueTypes (BitsType _), ValueTypes (BitsType _)
    | ValueTypes (FloatType _), ValueTypes (FloatType _) -> 
        Ok { rhs = operator expr1 expr2; typ = ValueTypes BoolType; range = rng }
    | t1, t2 when t1 = t2 && t1.IsPrimitiveAny ->
        Error [RelationalOperationOnAny (rng, expr1, expr2)] 
    //| t1, t2 when t1 = t2 -> 
    //    Error [MustBeRelational (rng, expr1, expr2)]
    | _, _ ->
        Error [RelationalTypesRequired (rng, expr1, expr2)] 
        

            
let private checkRelational operator (expr1: TypedRhs) (expr2: TypedRhs) =
    let e1 = tryPromotePrimitiveAny expr2.typ expr1
    let e2 = tryPromotePrimitiveAny expr1.typ expr2
    
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
        
        | t1, t2 when t1 = t2 && t1.IsPrimitiveAny ->
            Error [ArithmeticOperationOnAny (rng, expr1, expr2)]
        //| t1, t2 when t1 = t2 -> 
        //    Error [SameArithmeticTypeRequired(rng, expr1, expr2)]
        | _, _ -> 
            Error [ArithmeticTypesRequired (rng, expr1, expr2)]

    typ 
    |> Result.map ( fun t -> {rhs = operator expr1 expr2; typ = t; range = rng} )
 

/// Checks if literals and constant expression are of suitable size.
//let private andThen res1 res2 =
//    match res1 , res2 with
//    | Ok e1, Ok e2 -> Ok (e1, e2)
//    | Error e1, _ -> Error e1
//    | _, Error e2 -> Error e2


//let private checkArithmetic operator (expr1: TypedRhs) (expr2: TypedRhs) =
//    let e1 = amendPrimitiveAny expr2.typ expr1 
//    let e2 = e1 |> Result.bind (fun e1 -> amendPrimitiveAny e1.typ expr2)
    
//    andThen e1 e2
//    |> Result.bind (combineArithmeticOp operator)



/// Checks if literals and constant expression are of suitable size.
let private checkArithmetic operator (expr1: TypedRhs) (expr2: TypedRhs) =
    let e1 = tryAmendPrimitiveAny expr2.typ expr1
    let e2 = tryAmendPrimitiveAny expr1.typ expr2

    combine e1 e2
    |> Result.bind (combineArithmeticOp operator)


/// Returns the addition of two typed expressions or an error in case of type mismatch.
let private addition ((expr1: TypedRhs), (expr2: TypedRhs)) = 
    try 
        checkArithmetic add expr1 expr2
    with
    | :? System.OverflowException -> 
        let rng = Range.unionRanges expr1.Range expr2.Range
        Error [ArithmeticOverFlow (rng, expr1, expr2)]
        
/// Returns the subtraction of two typed expressions or an error in case of type mismatch.
let private subtraction ((expr1: TypedRhs), (expr2: TypedRhs)) = 
    try 
        checkArithmetic sub expr1 expr2
    with
    | :? System.OverflowException -> 
        let rng = Range.unionRanges expr1.Range expr2.Range
        Error [ArithmeticOverFlow (rng, expr1, expr2)]
        
/// Returns the product of two typed expressions or an error in case of type mismatch.
let private product ((expr1: TypedRhs), (expr2: TypedRhs)) =
    try 
        checkArithmetic mul expr1 expr2
    with
    | :? System.OverflowException -> 
        let rng = Range.unionRanges expr1.Range expr2.Range
        Error [ArithmeticOverFlow (rng, expr1, expr2)]
        
let private isZeroConstant (expr: TypedRhs) =
    match expr.rhs with
    | IntConst i -> i.IsZero
    | NatConst n -> n.IsZero
    | BitsConst b -> b.IsZero
    | FloatConst f -> f.IsZero
    | _ -> false

/// Returns the quotient of two typed expressions or an error in case of type mismatch.
let private quotient ((expr1: TypedRhs), (expr2: TypedRhs)) = 
    try
        if isZeroConstant expr2 then
            let rng = Range.unionRanges expr1.Range expr2.Range
            Error [DivideByZero (rng, expr2)] 
        else
            checkArithmetic div expr1 expr2
    with
    | :? System.DivideByZeroException  -> 
        failwith "Division by zero in evaluation should not occur"

/// Returns the remainder of integer division of two typed expressions or an error in case of type mismatch.
let private remainder ((expr1: TypedRhs), (expr2: TypedRhs)) = 
    try 
        match expr1.typ, expr2.typ with
        | ValueTypes (FloatType _), ValueTypes (FloatType _)
        | AnyFloat, ValueTypes (FloatType _)
        | ValueTypes (FloatType _), AnyFloat
        | AnyFloat, AnyFloat ->
            Error [CannotModFloats (expr1, expr2)]
        | _ -> 
            if isZeroConstant expr2 then 
                let rng = Range.unionRanges expr1.Range expr2.Range
                Error [DivideByZero (rng, expr2)]    
            else
                checkArithmetic modus expr1 expr2
    with
    | :? System.DivideByZeroException  -> 
        failwith "Division by zero in evaluation should not occur"
                
// --------------------------------------------------------------------
// ---  Type annotation in expr 'expr : type'
// --------------------------------------------------------------------

/// Checks if a type annotation has the same type as the expression
/// Literals are amended to the given type annotation 
let private typeAnnotation range (checkedExpr: TypedRhs, checkedType: Types) =
    let expr = 
        if checkedExpr.typ.IsCompoundLiteral then
            amendCompoundLiteral checkedType checkedExpr
        else 
            tryAmendPrimitiveAny checkedType checkedExpr        
    expr
    |> Result.bind (fun expr -> 
        match expr.typ, checkedType with
        | ValueTypes et, ValueTypes ct when et = ct ->
            Ok expr
        | ValueTypes _, ValueTypes _ -> 
            Error [ WrongTypeAnnotation (range, expr, checkedType) ] 
        | AnyComposite, _
        | AnyInt, _
        | AnyBits, _
        | AnyFloat, _ ->  
            Error [ LiteralDoesNotHaveType (range, checkedExpr, checkedType)]
        | _, _ ->
            failwith "Type annotation for unchecked or unsupported type"
        )
            

// --------------------------------------------------------------------
// ---  Cast operators 'as' and 'as!'
// --------------------------------------------------------------------

let private checkGuaranteedCasts range (primitiveExpr: TypedRhs) (simpleToType: Types) = 
    match primitiveExpr.typ, simpleToType with    
    // | ValueTypes (IntType i), ValueTypes (NatType n) when i.GetSize <= n.GetSize -> Ok primitiveExpr  // this is unsafe
    | ValueTypes (IntType i), ValueTypes (BitsType b) when i.GetSize <= b.GetSize -> Ok primitiveExpr
    | ValueTypes (IntType i), ValueTypes (FloatType f) when i.GetSize < f.GetSize -> Ok primitiveExpr
    | ValueTypes (IntType i), ValueTypes (IntType toI) when i <= toI -> Ok primitiveExpr
    
    | ValueTypes (NatType n), ValueTypes (IntType i) when n.GetSize < i.GetSize -> Ok primitiveExpr
    | ValueTypes (NatType n), ValueTypes (BitsType b) when n.GetSize <= b.GetSize -> Ok primitiveExpr
    | ValueTypes (NatType n), ValueTypes (FloatType f) when n.GetSize < f.GetSize -> Ok primitiveExpr
    | ValueTypes (NatType n), ValueTypes (NatType toN) when n <= toN -> Ok primitiveExpr
    
    | ValueTypes (BitsType b), ValueTypes (IntType i) when b.GetSize < i.GetSize -> Ok primitiveExpr
    | ValueTypes (BitsType b), ValueTypes (NatType n) when b.GetSize <= n.GetSize -> Ok primitiveExpr
    | ValueTypes (BitsType b), ValueTypes (FloatType f) when b.GetSize < f.GetSize -> Ok primitiveExpr
    | ValueTypes (BitsType b), ValueTypes (BitsType toB) when b <= toB -> Ok primitiveExpr
    
    | ValueTypes (FloatType f), ValueTypes (FloatType toF) when f <= toF -> Ok primitiveExpr
        
    | ValueTypes (IntType i), ValueTypes (IntType toI) when i > toI ->
        Error [ DownCast (range, primitiveExpr, simpleToType) ]
    | ValueTypes (NatType n), ValueTypes (NatType toN) when n > toN ->
        Error [ DownCast (range, primitiveExpr, simpleToType) ]
    | ValueTypes (BitsType b), ValueTypes (BitsType toB) when b > toB ->
        Error [ DownCast (range, primitiveExpr, simpleToType) ]
    | ValueTypes (FloatType f), ValueTypes (FloatType toF) when f > toF ->
        Error [ DownCast (range, primitiveExpr, simpleToType) ]

    | AnyBits, _ 
    | AnyInt, _ 
    | AnyFloat, _->
        Error [ LiteralCastNotAllowed (range, primitiveExpr, simpleToType) ]
        
    | ValueTypes vt1, ValueTypes vt2 ->
        Error [ ImpossibleGuaranteedCast (range, primitiveExpr, simpleToType) ]
    | _ ->
        failwith "Called with expr of non primitive types"        

/// Evaluates guaranteed cast on constants or forms the guaranteed cast
let private formGuaranteedCast range toType fromExpr =
    let rhs = 
        match fromExpr.rhs, toType with
        | IntConst i, ValueTypes (IntType it) -> IntConst <| Widen.IntToInt (i, it)
        | IntConst i, ValueTypes (NatType nt) -> NatConst <| Widen.IntToNat (i, nt)
        | IntConst i, ValueTypes (BitsType bt) -> BitsConst <| Widen.IntToBits (i, bt)
        | IntConst i, ValueTypes (FloatType ft) -> FloatConst <| Widen.IntToFloat (i, ft)
        | NatConst n, ValueTypes (NatType nt) -> NatConst <| Widen.NatToNat (n, nt)
        | NatConst n, ValueTypes (IntType it) -> IntConst <| Widen.NatToInt (n, it)
        | NatConst n, ValueTypes (BitsType bt) -> BitsConst <| Widen.NatToBits (n, bt)
        | NatConst n, ValueTypes (FloatType ft) -> FloatConst <| Widen.NatToFloat (n, ft)
        | BitsConst b, ValueTypes (BitsType bt) -> BitsConst <| Widen.BitsToBits (b, bt)
        | BitsConst b, ValueTypes (IntType it) -> IntConst <| Widen.BitsToInt (b, it)
        | BitsConst b, ValueTypes (NatType nt) -> NatConst <| Widen.BitsToNat (b, nt)
        | BitsConst b, ValueTypes (FloatType ft) -> FloatConst <| Widen.BitsToFloat (b, ft)
        | FloatConst f, ValueTypes (FloatType ft) -> FloatConst <| Widen.FloatToFloat (f, ft)
        | _ -> Convert (fromExpr, toType, Safe)   
    
    Ok {rhs = rhs; typ = toType; range = range}



let private checkForcedCasts range (primitiveExpr: TypedRhs) (simpleToType: Types) behaviour = 
    match primitiveExpr.typ, simpleToType with    
    // | ValueTypes (IntType i), ValueTypes (NatType n) when i.GetSize >= n.GetSize -> Ok primitiveExpr
    | ValueTypes (IntType _), ValueTypes (NatType _) -> Ok primitiveExpr  // This is always unsafe
    | ValueTypes (IntType i), ValueTypes (BitsType b) when i.GetSize >= b.GetSize -> Ok primitiveExpr
    | ValueTypes (IntType i), ValueTypes (FloatType f) when i.GetSize >= f.GetSize -> Ok primitiveExpr
    | ValueTypes (IntType i), ValueTypes (IntType toI) when i > toI -> Ok primitiveExpr

    | ValueTypes (NatType n), ValueTypes (IntType i) when n.GetSize >= i.GetSize -> Ok primitiveExpr
    | ValueTypes (NatType n), ValueTypes (BitsType b) when n.GetSize > b.GetSize -> Ok primitiveExpr
    | ValueTypes (NatType n), ValueTypes (FloatType f) when n.GetSize >= f.GetSize -> Ok primitiveExpr
    | ValueTypes (NatType n), ValueTypes (NatType toN) when n > toN -> Ok primitiveExpr

    | ValueTypes (BitsType b), ValueTypes (IntType i) when b.GetSize >= i.GetSize -> Ok primitiveExpr
    | ValueTypes (BitsType b), ValueTypes (NatType n) when b.GetSize > n.GetSize -> Ok primitiveExpr
    | ValueTypes (BitsType b), ValueTypes (FloatType f) when b.GetSize >= f.GetSize -> Ok primitiveExpr
    | ValueTypes (BitsType b), ValueTypes (BitsType toB) when b > toB -> Ok primitiveExpr

    | ValueTypes (FloatType f), ValueTypes (IntType _) -> Ok primitiveExpr
    | ValueTypes (FloatType f), ValueTypes (NatType _) -> Ok primitiveExpr
    | ValueTypes (FloatType f), ValueTypes (BitsType _) -> Ok primitiveExpr
    | ValueTypes (FloatType f), ValueTypes (FloatType toF) when f > toF -> Ok primitiveExpr

    | ValueTypes (IntType i), ValueTypes (IntType toI) when i <= toI ->
        Error [ ForcedUpCast (range, primitiveExpr, simpleToType) ]
    | ValueTypes (NatType n), ValueTypes (NatType toN) when n <= toN ->
        Error [ ForcedUpCast (range, primitiveExpr, simpleToType) ]
    | ValueTypes (BitsType b), ValueTypes (BitsType toB) when b <= toB ->
        Error [ ForcedUpCast (range, primitiveExpr, simpleToType) ]
    | ValueTypes (FloatType f), ValueTypes (FloatType toF) when f <= toF ->
        Error [ ForcedUpCast (range, primitiveExpr, simpleToType) ]

    | AnyBits, _ 
    | AnyInt, _ 
    | AnyFloat, _->
        Error [ LiteralCastNotAllowed (range, primitiveExpr, simpleToType) ]
        
    | ValueTypes vt1, ValueTypes vt2 ->
        Error [ ImpossibleForcedCast (range, primitiveExpr, simpleToType) ]
    | _, _ ->
        failwith "Called with expr of non primitive types"


/// Tries to evaluate forced cast on constants or forms the forced cast
/// Asserts that all forced casts are admissible
let private formForcedCast behaviour range toType fromExpr =
    let rhsResult =
        match fromExpr.rhs, toType with
        | IntConst i, ValueTypes (IntType intN) when intN.AllowsNarrowing i -> 
            Ok ( IntConst <| Narrow.IntToInt(i, intN) )
        | IntConst i, ValueTypes (NatType natN) when natN.AllowsNarrowing i ->
            Ok ( NatConst <| Narrow.IntToNat(i, natN) )
        | IntConst i, ValueTypes (BitsType bitsN) when bitsN.AllowsNarrowing i ->
            Ok ( BitsConst <| Narrow.IntToBits(i, bitsN) )
        | IntConst i, ValueTypes (FloatType floatN) when floatN.AllowsNarrowing i ->
            Ok ( FloatConst <| Narrow.IntToFloat(i, floatN) )
        | IntConst i, _ ->
            Error [ ForcedCastNotInType (range, fromExpr, toType) ]

        | NatConst n, ValueTypes (IntType intN) when intN.AllowsNarrowing n ->
            Ok ( IntConst <| Narrow.NatToInt(n, intN) )
        | NatConst n, ValueTypes (NatType natN) when natN.AllowsNarrowing n ->
            Ok ( NatConst <| Narrow.NatToNat(n, natN) )
        | NatConst n, ValueTypes (BitsType bitsN) when bitsN.AllowsNarrowing n ->
            Ok ( BitsConst <| Narrow.NatToBits(n, bitsN) )
        | NatConst n, ValueTypes (FloatType floatN) when floatN.AllowsNarrowing n ->
            Ok ( FloatConst <| Narrow.NatToFloat(n, floatN) )
        | NatConst n, _ ->
            Error [ ForcedCastNotInType (range, fromExpr, toType) ]

        | BitsConst b, ValueTypes (IntType intN) when intN.AllowsNarrowing b ->
            Ok ( IntConst <| Narrow.BitsToInt(b, intN) )
        | BitsConst b, ValueTypes (NatType natN) when natN.AllowsNarrowing b ->
            Ok ( NatConst <| Narrow.BitsToNat(b, natN) )
        | BitsConst b, ValueTypes (BitsType bitsN) when bitsN.AllowsNarrowing b ->
            Ok ( BitsConst <| Narrow.BitsToBits(b, bitsN) )
        | BitsConst b, ValueTypes (FloatType floatN) when floatN.AllowsNarrowing b ->
            Ok ( FloatConst <| Narrow.BitsToFloat(b, floatN) )
        | BitsConst b, _ ->
            Error [ ForcedCastNotInType (range, fromExpr, toType) ]

        | FloatConst f, ValueTypes (IntType intN) when intN.AllowsNarrowing f ->
            Ok ( IntConst <| Narrow.FloatToInt(f, intN) )
        | FloatConst f, ValueTypes (NatType natN) when natN.AllowsNarrowing f ->
            Ok ( NatConst <| Narrow.FloatToNat(f, natN) )
        | FloatConst f, ValueTypes (BitsType bitsN) when bitsN.AllowsNarrowing f ->
            Ok ( BitsConst <| Narrow.FloatToBits(f, bitsN) )
        | FloatConst f, ValueTypes (FloatType floatN) when floatN.AllowsNarrowing f ->
            Ok ( FloatConst <| Narrow.FloatToFloat(f, floatN) )
        | FloatConst f, _ ->
            Error [ ForcedCastNotInType (range, fromExpr, toType) ]

        | _ -> 
            Ok <| Convert (fromExpr, toType, behaviour)

    rhsResult
    |> Result.bind (fun rhs -> Ok { rhs = rhs; typ = toType; range = range })          


let private conversion behaviour range (checkedExpr: TypedRhs, checkedToType: Types) =
    if checkedToType.IsPrimitive && (checkedExpr.typ.IsPrimitive || checkedExpr.typ.IsPrimitiveAny) then
        match behaviour with
        | Safe ->
            checkGuaranteedCasts range checkedExpr checkedToType
            |> Result.bind (formGuaranteedCast range checkedToType)
        | Unsafe
        | Throwing ->
            checkForcedCasts range checkedExpr checkedToType behaviour
            |> Result.bind (formForcedCast behaviour range checkedToType)
    else
        Error [ ImpossibleCast (range, checkedExpr, checkedToType) ]

//=============================================================================
// Checking right and left hand side usages (expressions)
// A function call can be the rhs of an expression and is hence tightly coupled
// with checkExpr.
//=============================================================================

/// Check that arguments in the output position match the number and type of
/// the formal parameters.
let internal checkOutputs (lut: TypeCheckContext) pos (outputArgs: Result<_,_> list) declName (outputParams: ParamDecl list) =
    let rec typecheckOutputs = function
        | [] -> []
        | ((paramDecl: ParamDecl), (argExpr: TypedLhs))::ls -> 
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
let internal checkInputs pos (inputArgs: Result<_,_> list) declName (inputParams: ParamDecl list) =
    let rec typecheckInputs = function
        | [] -> []
        | ((argDecl: ParamDecl), (expr: TypedRhs))::ls -> 
            match amendRhsExpr argDecl.datatype expr with // this behaves like an initialisation
            | Ok amendedExpr ->
                if argDecl.datatype.IsValueType || isExprALocation amendedExpr then
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
    | AST.Bool (value = bc; range = pos) -> { rhs = BoolConst bc; typ = ValueTypes BoolType; range = pos } |> Ok
    // -- numerical constants --
    | AST.Int (value, _, pos) -> 
        if Int64.CanRepresent value || Nat64.CanRepresent value then // Int literals allow an unary minus in attributes
            { rhs = IntConst value; typ = AnyInt; range = pos } |> Ok
        else
            Error [NumberLargerThanAnyInt(pos, value)]
    | AST.Bits (bits, pos) ->
        if Bits64.CanRepresent bits then // Bits literals are always >= 0                     
            { rhs = BitsConst bits; typ = AnyBits; range = pos } |> Ok
        else
            Error [NumberLargerThanAnyBits(pos, bits)]                 
    | AST.Float (number, _, pos) ->
        if Float64.CanRepresent number then // Float literals allow an unary minus in attributes
            { rhs = FloatConst number; typ = AnyFloat; range = pos } |> Ok
        else
            Error [NumberLargerThanAnyFloat(pos, number)]
    | AST.String _ 
    | AST.MultiLineString _->
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
            let checkIdx idx =
                checkExpr lut idx 
                |> Result.bind (evalCompTimeIndex lut)
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
                        :: checkFields (thisFieldNum + Constants.SizeOne) rest // continue with the next array index
                    | Error x -> [Error x] // in case of error, just wrap it in a list and stop recursion
            
            checkFields Constants.SizeZero fields
            |> contract
            |> Result.map (fun ckdFields -> { rhs = ArrayConst ckdFields; typ = AnyComposite; range = r})

/// Translate a dynamic access path to a typed memory location
and private checkUntimedDynamicAccessPath lut dname =
    let qname, subexpr = lut.ncEnv.GetLookupTable.decomposeDpath dname
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
                    | ValueTypes (ValueTypes.StructType (typname, typfields))
                    | ReferenceTypes (ReferenceTypes.StructType(_, typname, typfields)) ->
                        typfields
                        |> List.tryFind (fun f -> f.name.basicId = name.id)
                        |> function
                            | None -> Error [FieldNotAMember(name, tml)]
                            | Some varDecl -> Ok (tml.AddFieldAccess name.id, varDecl.datatype)
                    | _ -> Error [FieldAccessOnNonStructType(name, tml)]
                )
            | AST.Index (idx, r) ->
                let isIndexType = function
                    | AnyInt
                    | AnyBits
                    | ValueTypes (IntType _)
                    | ValueTypes (BitsType _)
                    | ValueTypes (NatType _) -> true
                    | _ -> false
                // check that tml is actually an array
                tmlAndType
                |> Result.bind (fun (tml,typ) -> // given a valid type
                    match typ with
                    | ValueTypes (ArrayType (asize, dty)) -> // ensure it is an array type
                        checkExpr lut idx
                        |> Result.bind (fun trhs -> // evaluate the index expression
                            if isIndexType trhs.typ then // make sure it is an int, nat or bits
                                match tryEvalCompTimeIndex lut trhs with // if it is constant we can even check boundaries
                                | Ok (Some actualIndex) ->
                                    if Constants.SizeZero <= actualIndex && actualIndex < asize then
                                        Ok (tml.AddArrayAccess trhs, ValueTypes dty)
                                    else
                                        Error [ StaticArrayOutOfBounds(dname.Range, trhs, tml.AddArrayAccess trhs, asize - SizeOne) ] // -1 since we need the maximal index in the error message
                                | Ok (None) -> // the index is determined at runtime
                                    if isConstVarDecl lut tml then // but then the array must not be constant
                                        Error [ConstArrayRequiresConstIndex dname.Range]  
                                        // TODO: Should structured constants have a representation in memory? fjg. 24.02.20
                                        // Currently the backend normalises accesses to constants and crashes if this not tested.
                                    else // param/let/var array with dynamic access, Ok
                                        Ok (tml.AddArrayAccess trhs, ValueTypes dty)
                                | Error e ->
                                    Error e
                            else
                                Error [IndexMustBeInteger(dname.Range, trhs, tml.AddArrayAccess trhs)] // Todo: Better error message, fjg. 24.02.20
                            )
                    | _ -> Error [ArrayAccessOnNonArrayType(r, tml)]
                    )
            | AST.StaticIndex _ ->
                Error [UnsupportedFeature (acc.Range, "static array indices or optionals")]
        List.fold processAccessOn tmlInit accesses


/// Shorthand helper. Given two expressions e1, e2 and a combination 
/// function f (and, or, +, -, ...), 
/// typecheck e1 and e2 and combine
/// using f.
and private combineTwoExpr lut (e1: AST.Expr) (e2: AST.Expr) f =
    combine (checkExpr lut e1) (checkExpr lut e2)
    |> Result.bind f


/// Shorthand helper. Given two expressions bits and amount, and a shift 
/// function shiftFun (<<, >>, +>>, <>>, <<>), 
/// typecheck bits and amount and combine
/// using shf.
and private combineShift lut (bits: AST.Expr) (amount: AST.Expr) shiftFun =
    combine (checkExpr lut bits) (checkExpr lut amount)
    |> Result.bind (shiftFun lut)


/// Shorthand helper. Given expressions expr and type typ 
/// and a cast or conversion function reTypeFun
/// type check expr and typ and combine
/// using reTypeFun.
and private combineExprAndType lut (expr: AST.Expr) (typ: AST.DataType) reTypeFun =
    let rng = Range.unionRanges expr.Range typ.Range
    combine (checkExpr lut expr) (checkDataType lut typ)
    |> Result.bind (reTypeFun rng)


/// Given an untyped AST.Expr, return a typed expression.
/// We guarantee that compile time expressions are evaluated to a literal
/// BoolConst, IntConst, FloatConst, ResetConst, StructConst, ArrayConst
/// where the latter two may only contain const literals in their fields recursively.
and internal checkExpr (lut: TypeCheckContext) expr = 
    match expr with
    | AST.Expr.Const literal -> checkSimpleLiteral literal
    | AST.Expr.AggregateConst (ac, r) -> checkAggregateLiteral lut ac r
    | AST.Expr.SliceConst (_, _, _, r) -> Error [UnsupportedFeature (r, "slice const")] // TODO
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
                    | Declarable.ProcedureImpl _
                    | Declarable.ProcedurePrototype _ -> failwith "QName prefix of a TML cannot point to a subprogram!"
                | ReferenceTypes _
                | Any
                | AnyComposite 
                | AnyInt
                | AnyBits 
                | AnyFloat -> Error [PrevOnlyOnValueTypes(expr.Range, dty)]
        checkUntimedDynamicAccessPath lut dname
        |> Result.bind makeTimedRhsStructure
    // -- function call --
    | AST.FunctionCall (fp, readArgs, writeArgs, r) ->
        let resIn = List.map (checkExpr lut) readArgs
        let resOut = List.map (checkLExpr lut) writeArgs
        checkFunCall false lut r fp resIn resOut
        |> Result.bind(fun (f, t) -> {rhs = RhsStructure.FunCall f; typ = ValueTypes t; range = r} |> Ok)
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

    // relational operators

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
    
    
    // bitwise operators
    | AST.Bnot (subexpr, r) ->
        checkExpr lut subexpr
        |> Result.bind (complement r)
    | AST.Bor (e1, e2) -> combineTwoExpr lut e1 e2 bitwiseOr
    | AST.Band (e1, e2) -> combineTwoExpr lut e1 e2 bitwiseAnd
    | AST.Bxor (e1, e2) -> combineTwoExpr lut e1 e2 bitwiseXor
    | AST.Shl (e1, e2) -> combineShift lut e1 e2 shiftLeft
    | AST.Shr (e1, e2) -> combineShift lut e1 e2 shiftRight

    // Advance bitwise operators
    | AST.Sshr (e1, e2) -> combineShift lut e1 e2 signedShiftRight
    | AST.Rotl (e1, e2) -> combineShift lut e1 e2 rotateLeft
    | AST.Rotr (e1, e2) -> combineShift lut e1 e2 rotateRight

    // identity operators
    | AST.Ideq _ 
    | AST.Idieq _ ->
        Error [UnsupportedFeature (expr.Range, "identity operator")]
    
    // type conversion and annotation
    | AST.Convert (e, t, b) -> combineExprAndType lut e t (conversion b)
    | AST.HasType (e, t) -> combineExprAndType lut e t typeAnnotation
    
    // operators on arrays and slices
    | AST.Len _
    | AST.Cap _ -> //TODO
        Error [UnsupportedFeature (expr.Range, "length or capacity")]
    // parentheses
    | AST.Expr.Parens (expr, rng) ->
        checkExpr lut expr
        |> Result.map (fun e -> e.SetRange rng) 

    |> Result.map (tryEvalConst lut)

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
        checkExpr lut size
        |> Result.bind (evalCompTimeSize lut)
        |> Result.bind(fun checkedSize ->
            checkDataType lut elemDty
            |> Result.bind(fun dty -> 
                match dty with
                | ValueTypes sth ->
                    ArrayType (checkedSize, sth) |> ValueTypes |> Ok
                | _ -> 
                    Error [ValueArrayMustHaveValueType pos]
                )
            )
    | AST.TypeName spath ->
        // look up given static name in the dict of known named types (user types)
        // TODO: Create a lookup function in TypeCheckContext and return the result here, fjg. 24.02.20
        let found, res =
            lut.ncEnv.GetLookupTable.spathToQname spath
            |> lut.userTypes.TryGetValue
        if found then Ok (snd res)
        else Error [ NotInLUTPrevError spath.dottedPathToString ]
    // unsupported now:
    | AST.SliceType _
    | AST.Signal _ -> 
        Error [UnsupportedFeature (utyDataType.Range, "types other than bool, int, nat, float, fixed size array or user defined struct")]

/// Type check expressions that appear on the left hand side.
and internal checkLExpr lut (dname: AST.DynamicAccessPath) =
    let makeTimedLhsStructure ( tml, dty ) =
        match dname.timepoint with
        | AST.TemporalQualification.Current -> 
            Ok {lhs = LhsCur tml; typ = dty; range = dname.Range}
        | AST.TemporalQualification.Previous r -> 
            Error [PrevOnLhs (r, dname.pathToString)]
        | AST.TemporalQualification.Next _ ->  
            Ok {lhs = LhsNext tml; typ = dty; range = dname.Range}
    checkUntimedDynamicAccessPath lut dname
    |> Result.bind makeTimedLhsStructure


and internal checkAssignLExpr lut lhs =
    match lhs with
    | AST.Wildcard _ -> 
        Ok { lhs = Wildcard; typ = Any; range = lhs.Range }
    | AST.Loc dname ->
        checkLExpr lut dname
    


/// Type check functions calls.
/// A function call can either appear as a statement and then must call a void function.
/// Or a function call can be part of an expression and then the called function must return a non-void, first class value.
and internal checkFunCall isStatement (lut: TypeCheckContext) pos (fp: AST.Code) (inputs: Result<_,_> list) (outputs: Result<_,_> list) =
    let checkIsFunction (decl: ProcedurePrototype) =
        if decl.IsFunction then Ok()
        elif decl.IsActivity then
            Error [FunCallToAct(pos, decl)]
        else
            Error [FunNotExist(pos, decl)]

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
        |> Result.map lut.ncEnv.GetLookupTable.dpathToQname
        |> Result.bind (getSubProgDeclAsPrototype lut pos)
        |> Result.bind (fun decl ->
            checkIsFunction decl
            |> combine <| checkInputs pos inputs decl.name decl.inputs
            |> combine <| checkOutputs lut pos outputs decl.name decl.outputs
            |> combine <| checkReturnType decl.name decl.returns
            |> Result.map (createCall (decl.name, decl.returns))
            )


/// Check that condition is a boolean, side-effect free expression
let internal fCondition lut cond = 
    let ensureBoolean (e: TypedRhs) =
        match e.typ with
        | ValueTypes BoolType -> Ok e
        | _ -> Error [ExpectedBoolExpr (e.Range, e)]
    let ensureSideEffectFree (e: TypedRhs) =
        if hasNoSideEffect lut e then Ok e
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