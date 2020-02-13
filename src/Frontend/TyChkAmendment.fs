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

///============================================================================
/// This module collects functions that operate on already typed Blech
/// types and expression structures.
/// Internal functions are provided for the other type checker modules to
/// fill up or combine incomplete (but typed) expressions.
///============================================================================
module Blech.Frontend.TyChkAmendment

open Constants
open CommonTypes
open BlechTypes
open TyChecked

module Range = Blech.Common.Range


/// Returns yes if the expression contains at least one name
/// This is useful for type checking where we want to make sure that
/// in a variable declaration such as "var x = 8", we do not merely
/// look at the type of "8" which is int8 and falsely make x an int8
/// as well but instead give an error to the user.
//let rec private exprContainsName rhs =
//    let recurFields fs = 
//        fs 
//        |> List.map (fun (_, xs) -> exprContainsName xs.rhs)
//        |> List.forall id
    
//    match rhs with
//    // names
//    | RhsCur _ | Prev _ | FunCall _ -> true
//    // simple literals
//    | BoolConst _ | IntConst _ | FloatConst _ | ResetConst -> false
//    // composite literals
//    | StructConst rhsList -> rhsList |> recurFields
//    | ArrayConst elems -> elems |> recurFields
//    // subexpressions
//    // unary
//    | Neg a | Bnot a -> exprContainsName a.rhs
//    // logical
//    | Conj (a, b) | Disj (a, b)
//    // bitwise
//    | Band (a, b) | Bor (a, b) | Bxor (a, b)
//    | Shl (a, b) | Shr (a, b) | Sshr (a, b) | Rotl (a, b) | Rotr (a, b)
//    // relational
//    | Les (a, b) | Leq (a, b) | Equ (a, b) 
//    // arithmetic
//    | Add (a, b) | Sub (a, b) | Mul (a, b) | Div (a, b) | Mod (a, b) ->
//        exprContainsName a.rhs || exprContainsName b.rhs


/// Whenever a composite data type is re-/initialised we need to determine
/// the default initialiser and merge it with whatever the user has written
/// on the right hand side of the =.
let internal unsafeMergeCompositeLiteral deflt user =
    let mkUniqueInit ds us =
        us @ ds |> List.distinctBy fst
    
    match deflt, user with
    | StructConst defPairs, StructConst userPairs -> 
        mkUniqueInit defPairs userPairs
        |> StructConst
    | ArrayConst defPairs, ArrayConst userPairs ->
        mkUniqueInit defPairs userPairs
        |> ArrayConst
    | ResetConst, x 
    | x, ResetConst -> 
        x
    | _ -> failwith "Whatever we are trying to merge here are neither array nor struct literals."

/// Return true iff typL is a supertype of or equal to typR
/// E.g. Int32 is supertype of Int8
// TODO: Rename this function to something more appropriate, fjg. 29.01.20
let internal isLeftSupertypeOfRight typL typR =
    match typL, typR with
    | ValueTypes (IntType sizeL), ValueTypes (IntType sizeR) ->
        sizeL >= sizeR
    | ValueTypes (NatType sizeL), ValueTypes (NatType sizeR) ->
        sizeL >= sizeR
    | ValueTypes (BitsType sizeL), ValueTypes (BitsType sizeR) ->
        sizeL >= sizeR
    | ValueTypes (FloatType sizeL), ValueTypes (FloatType sizeR) -> 
        sizeL >= sizeR

    | ValueTypes (IntType _), AnyInt
    | ValueTypes (NatType _), AnyInt
    | ValueTypes (BitsType _), AnyInt
    | ValueTypes (FloatType _), AnyInt 
    | ValueTypes (BitsType _), AnyBits
    | ValueTypes (NatType _), AnyBits
    | ValueTypes (FloatType _), AnyFloat -> true

    | Any, _ -> true      // wildcard hast type Any which is supertype of any other type

    | a, b when (a = b) -> true
    
    | _, _ -> false // this includes the cases that integers shall not 
                    // implicitly be promoted to floats


/// Returns default value for given datatype.
/// Contains superflous 0 entries, use getInitValueWithoutZeros
/// to obtain the "minimal" default value for composite 
/// pos and name are for error messages only
let rec getDefaultValueFor pos name dty =
    match dty with
    | Any
    | AnyComposite 
    | AnyInt 
    | AnyBits 
    | AnyFloat -> 
        Error [NoDefaultValueForAny (pos, name)]
    | ValueTypes fce ->
        match fce with
        | Void -> Error [IllegalVoid (pos, name)]                                
        | BoolType -> Ok {rhs = BoolConst false; typ = dty; range = pos}
        | IntType size -> Ok {rhs = IntConst <| Evaluation.Constant.IntZero size; typ = dty; range = pos}
        | BitsType size -> Ok {rhs = BitsConst <| Evaluation.Constant.BitsZero size; typ = dty; range = pos}
        | NatType size -> Ok {rhs = NatConst <| Evaluation.Constant.NatZero size; typ = dty; range = pos}
        | FloatType size ->Ok {rhs = FloatConst <| Evaluation.Constant.FloatZero size; typ = dty; range = pos}
        | ValueTypes.StructType (_, _, fields) ->
            let defaultValues =
                fields
                |> List.map (fun f -> f.name.basicId, f.initValue)
            Ok {rhs = StructConst defaultValues; typ = dty; range = pos}
        | ValueTypes.ArrayType (size, elemDty) ->
            getDefaultValueFor pos name (ValueTypes elemDty)
            |> Result.map (fun v -> [ for i in SizeZero .. SizeOne .. size - SizeOne -> (i, v) ])
            |> Result.map (fun lst -> { rhs = ArrayConst lst; typ = dty; range = pos })
    | ReferenceTypes s ->
        Error [NoDefaultValueForSecondClassType (pos, name, s)]

  

/// Returns the default initial value of a value type where
/// 0's are removed from composite literals.
/// E.g. {a=[[0]=0, [1]=0, [2]=0], b=[[0]=0, [1]=7, [2]=0]} becomes {b=[[1]=7]}
let internal getInitValueWithoutZeros pos name dty =
    let rec isNonZero expr =
        let filterOutZeroFields assignments constBuilder =
            assignments                 // list of given cell or field initialisers
            |> List.choose(fun (i,e) -> // choose the non-0 initialisers only
                isNonZero e
                |> Option.map(fun x -> i, x)
                )
            |> function                 // are any field initialisers left?
                | [] -> None
                | xs -> Some {expr with rhs = constBuilder xs}
        match expr.rhs with
        | BoolConst false -> None
        | IntConst value when value.IsZero -> None
        | BitsConst value when value.IsZero-> None
        | FloatConst value when value.IsZero -> None
        | ResetConst -> None 
        | StructConst assignments -> filterOutZeroFields assignments StructConst
        | ArrayConst assignments -> filterOutZeroFields assignments ArrayConst
        | _ -> Some expr
    
    let eliminateZeros expr =
        let filterEmptyLiterals constBuilder =
            isNonZero expr
            |> function
                | None -> {expr with rhs = constBuilder []}
                | Some e -> e
        match expr.rhs with
        | StructConst _ -> filterEmptyLiterals StructConst
        | ArrayConst _ -> filterEmptyLiterals ArrayConst
        | _ -> expr
    
    getDefaultValueFor pos name dty
    |> Result.map eliminateZeros


//=============================================================================
// Functions that map already type checked expressions further
// depending on the context. We distinguish "amendment" and "alignment".
// Amending means to fill up a given composite literal to the minimal literal
// which correctly initialises all non-zero fields of the data structure.
// Aligning means to infer the type of the lhs from the rhs or vice versa.
//=============================================================================

/// Amends a struct literal depending on the lhs type
/// inInitMode - true iff lhs and rhs a parts of a declaration (initialisation)
/// lTyp - type of the lhs
/// pos - range of the literal we are trying to amend
/// name - struct's type name, only needed for error messages
/// fields - list of VarDecls inside a struct
/// kvps - list of key-value pairs in the rhs struct literal
let rec private amendStruct inInitMode lTyp pos name (fields: VarDecl list) kvps =
    let merge checkedUserInput = 
        getInitValueWithoutZeros pos name.basicId lTyp
        |> Result.map (fun r -> unsafeMergeCompositeLiteral r.rhs (StructConst checkedUserInput))
        |> function
            | Ok (StructConst s) -> s
            | Ok ResetConst -> []
            | Ok _
            | Error _ -> failwith "Failed merging struct literals"
    
    let processKvp kvp =
        // does such a field exist?
        fields
        |> List.tryFindIndex (fun field -> fst kvp = field.name.basicId)
        |> function
            | None -> // no
                Error [FieldNotAMember2(pos, name, fst kvp)]
            | Some idx -> // yes, do the checks, take the RhsExpr
                if fields.[idx].mutability.Equals Mutability.Variable || inInitMode then // check mutability of the field
                    // recursively check and amend the rhs expr
                    amendRhsExpr inInitMode fields.[idx].datatype (snd kvp)
                    |> Result.map (fun amendedRhs -> (fst kvp, amendedRhs))
                else // writing to let field
                    Error [AssignmentToImmutable(pos, fields.[idx].name.basicId)]
    
    kvps                   // type checked key value pairs as given by the programmer
    |> List.map processKvp // check that each kvp belongs to this struct
    |> contract
    |> Result.map(
        merge // fill up all non-0 values that were not specified by the programmer
        >> (fun (literal) -> { rhs = StructConst literal; typ = lTyp; range = pos })
        )


/// Amends an array literal depending on the lhs type
/// inInitMode - true iff lhs and rhs a parts of a declaration (initialisation)
/// lTyp - type of the lhs
/// pos - range of the literal we are trying to amend
/// size - array's length
/// datatype - array's elements' type
/// kvps - list of index-value pairs in the rhs array literal
and private amendArray inInitMode lTyp pos (size: Size) datatype (kvps: (Size * TypedRhs) list) =
    let merge checkedUserInput = 
        getInitValueWithoutZeros Range.range0 "" lTyp // TODO: this is a hacky use of API, fg 16.04.19
        |> Result.map (fun r -> unsafeMergeCompositeLiteral r.rhs (ArrayConst checkedUserInput))
        |> function
            | Ok (ArrayConst s) -> s
            | Ok ResetConst -> []
            | Ok _
            | Error _ -> failwith "Failed merging array literals."
    
    // check there are no more element initialisers than the size of array
    try 
        if kvps.Length <= int size && (List.last kvps |> fst) < size then 
            // check all elements fit datatype
            let indices, values = kvps |> List.unzip
                     
            values 
            |> List.map (amendRhsExpr inInitMode (ValueTypes datatype))
            |> contract
            |> Result.map (
                List.zip indices
                >> merge // fill up array initialisers if necessary
                >> (fun literal -> { rhs = ArrayConst literal; typ = lTyp; range = pos })
                )
        else
            Error [TooManyInitialisers(pos, size)]
    with
        | :? System.OverflowException ->  
            failwith "Array literal with more elements than an int can represent" // this will certainly never happen


and internal amendPrimitiveAny toTyp (any: TypedRhs)  = 
    match any.typ, toTyp with
    | AnyInt , ValueTypes (IntType intX) ->
        let value = any.rhs.GetIntConst
        if intX.CanRepresent value then 
            Ok {any with rhs = IntConst <| intX.AdoptAny value ; typ = toTyp}
        else
            Error[NumberLargerThanAnyInt (any.Range, value.ToString())]  // TODO: better error message, fjg. 28.01.20            

    | AnyInt, ValueTypes (NatType natX) ->
        let value = any.rhs.GetIntConst
        if natX.CanRepresent value then
            Ok {any with rhs = NatConst <| natX.AdoptAny value; typ = toTyp }
        else
            Error[NumberLargerThanAnyInt (any.Range, value.ToString())]  // TODO: better error message, fjg. 28.01.20            
            
    | AnyInt, ValueTypes (BitsType bitsX) ->
        let value = any.rhs.GetIntConst
        if bitsX.CanRepresent value then
            Ok {any with rhs = BitsConst <| bitsX.AdoptAny value; typ = toTyp}
        else
            Error[NumberLargerThanAnyInt (any.Range, value.ToString())]  // TODO: better error message, fjg. 28.01.20     
            
    | AnyInt, ValueTypes (FloatType floatX) ->
        let value = any.rhs.GetIntConst
        if floatX.CanRepresent value then
            Ok {any with rhs = FloatConst <| floatX.AdoptAny value; typ = toTyp}
        else
            Error[NumberLargerThanAnyInt (any.Range, value.ToString())]  // TODO: better error message, fjg. 28.01.20     
    
    | AnyBits, ValueTypes (BitsType bitsX) ->
        let value = any.rhs.GetBitsConst
        if bitsX.CanRepresent value then
            Ok {any with rhs = BitsConst <| bitsX.AdoptAny value; typ = toTyp}
        else
            Error[NumberLargerThanAnyInt (any.Range, value.ToString())]  // TODO: better error message, fjg. 28.01.20            

    | AnyBits, ValueTypes (NatType natX) ->
        let value = any.rhs.GetBitsConst
        if natX.CanRepresent value then
            Ok {any with rhs = NatConst <| natX.AdoptAny value; typ = toTyp}
        else
            Error[NumberLargerThanAnyInt (any.Range, value.ToString())]  // TODO: better error message, fjg. 28.01.20            

    | AnyFloat, ValueTypes (FloatType floatX) ->
        let value = any.rhs.GetFloatConst
        if floatX.CanRepresent value then
            Ok {any with rhs = FloatConst <| floatX.AdoptAny value; typ = toTyp}
        else
            Error[NumberLargerThanAnyInt (any.Range, value.ToString())]  // TODO: better error message, fjg. 28.01.20              
    
    | _, _  ->
        Ok any

        
/// With structured literals we may need to "fill them up" since a user may 
/// provide only some of the structure or array fields.
/// inInitMode - true if this function is called from an initialisation
///              here also immutable fields may be set
/// lTyp       - type of the left hand side that we write the literal to
/// rExpr      - the given (partial) literal
and internal amendRhsExpr inInitMode lTyp (rExpr: TypedRhs) =
    // if rhs type is at least as concrete as on the lhs, we are satisfied
    if isLeftSupertypeOfRight lTyp rExpr.typ then
        // if left hand side is _, its type is any and we need to keep the rhs type
        // if right hand side is 8 or 4.2f, we need to take the more concrete type of the lhs
        // if we write _ = 7 amending fails
        if lTyp.IsWildcard && rExpr.typ.IsSomeAny then     
            Error [VarDeclMissingTypeOrValue (rExpr.range, rExpr.ToString())]
        elif lTyp.IsWildcard then 
            Ok rExpr
        elif rExpr.typ.IsPrimitiveAny then // primitive any
            amendPrimitiveAny lTyp rExpr
        else 
            Ok {rExpr with typ = lTyp}
    // otherwise we are lacking information about the rhs
    // this is the case with struct literals or reset literals, array literals
    // these have to be filled up and their type needs to be updated
    elif rExpr.typ.IsCompoundLiteral then // we expect to be amending only Any typed expressions (literals, in fact)
        match lTyp, rExpr.rhs with
        // resetting
        | ValueTypes (ValueTypes.StructType _), ResetConst
        | ValueTypes (ArrayType _), ResetConst ->
            // build a struct (or resp. array) const with default values of the fields
            // note that we do overwrite let fields but we do so with the default value which essentially has no effect
            getInitValueWithoutZeros rExpr.Range "" lTyp
        // structs
        | ValueTypes (ValueTypes.StructType (_, name, fields)), StructConst assignments ->
            amendStruct inInitMode lTyp rExpr.Range name fields assignments 
        // arrays
        | ValueTypes (ArrayType (size, datatype)), ArrayConst idxValPairs ->
            amendArray inInitMode lTyp rExpr.Range size datatype idxValPairs
        // all sorts of mismatches
        | ValueTypes (ArrayType _), StructConst _ ->
            Error [TypeMismatchArrStruct(lTyp, rExpr)]
        | ValueTypes (ValueTypes.StructType _), ArrayConst _ ->
            Error [TypeMismatchStructArr(lTyp, rExpr)]
        | t, _ when t.IsPrimitive->
            Error [TypeMismatchPrimitiveComposite(lTyp, rExpr)]
        // altering reference typed data is illegal
        | ReferenceTypes (ReferenceTypes.StructType _), ResetConst _
        | ReferenceTypes (ReferenceTypes.StructType _), StructConst _ ->
            Error [CannotResetRefType(rExpr.Range)]
        // at this point we've missed something
        | _ -> Error [AmendBroken(lTyp, rExpr)]
    else
        Error [TypeMismatch(lTyp, rExpr)]


/// Poor man's type deduction for variable initialisation.
/// If either type or initial value is given, infer the other one if possible.
/// If both are given, check that the types agree.
let internal alignOptionalTypeAndValue pos name dtyOpt (initValOpt: TyChecked<TypedRhs> option) =
    let inferFromRhs (expr: TypedRhs) =
        // we need to infer the data type from the right hand side initialisation expression
        // however if that is a literal we might have not enough information (which int size?)
        match expr.typ with
        | Any // wildcard
        | AnyComposite // struct/array const literals
        | AnyInt 
        | AnyBits
        | AnyFloat ->
            Error [VarDeclRequiresExplicitType (pos, name)]    
        //| ( ValueTypes (IntType _) 
        //  | ValueTypes (FloatType _) ) when not (exprContainsName expr.rhs) ->
        //    Error [VarDeclRequiresExplicitType (pos, name)]
        | _ ->
            Ok (expr.typ, expr)

    match dtyOpt, initValOpt with
    | None, None ->
        Error [VarDeclMissingTypeOrValue (pos, name)]
    | None, Some vRes -> 
        vRes |> Result.bind inferFromRhs
    | Some dtyRes, None ->
        dtyRes 
        |> Result.map (getInitValueWithoutZeros pos name)
        |> Result.bind (combine dtyRes)
    | Some dtyRes, Some vRes ->
        combine dtyRes vRes
        |> Result.bind (fun (dty, v) ->
            amendRhsExpr true dty v
            |> Result.map (fun amendedV -> (dty, amendedV))
        )