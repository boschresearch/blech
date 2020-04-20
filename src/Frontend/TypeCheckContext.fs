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

//=============================================================================
// Lookup table and associated functions
//=============================================================================

namespace Blech.Frontend

open Blech.Common
open System.Collections.Generic
open CommonTypes
open BlechTypes


/// Aggregates all typed Blech types which represent some sort of declaration.
/// This is needed for the lookup table.
type Declarable =
    | ParamDecl of ParamDecl
    | VarDecl of VarDecl
    | ExternalVarDecl of ExternalVarDecl
    | SubProgramDecl of SubProgramDecl
    | FunctionPrototype of FunctionPrototype
    
    member this.GetQName() =
        match this with
        | ParamDecl {name = x}
        | VarDecl {name = x} 
        | ExternalVarDecl {name = x}
        | SubProgramDecl {name = x}
        | FunctionPrototype {name = x} -> x
    
    member this.GetLn() =
        match this with
        | ParamDecl {pos = x}
        | VarDecl {pos = x}
        | ExternalVarDecl {pos = x}
        | SubProgramDecl {pos = x} 
        | FunctionPrototype {pos = x} -> x
    
    member this.TryGetDefault() =
        match this with
        | VarDecl {initValue = x} -> Some x
        | ExternalVarDecl _ // externals have no default value
        | ParamDecl _
        | SubProgramDecl _
        | FunctionPrototype _ -> None

    member this.TryGetMutability =
        match this with
        | VarDecl {mutability = x}
        | ExternalVarDecl {mutability = x} -> Some x
        | ParamDecl {isMutable = x} -> if x then Some Mutability.Variable else Some Mutability.Immutable
        | SubProgramDecl _
        | FunctionPrototype _ -> None
    
    member this.AddReference pos =
        match this with
        | ParamDecl {allReferences = ar}
        | VarDecl {allReferences = ar}
        | ExternalVarDecl {allReferences = ar}
        | SubProgramDecl {allReferences = ar}
        | FunctionPrototype {allReferences = ar} ->
            ar.Add pos


/// The lookup table.
/// Provides a link between a qualified name and its typed declaration.
/// This allows to lookup what type an identifier has or the position it is declared.
type TypeCheckContext = 
    { 
        cliContext: Arguments.BlechCOptions
        ncEnv: SymbolTable.LookupTable
        nameToDecl: Dictionary<QName, Declarable>
        // user types are required to resolve new types or type aliases defined in terms of user types
        userTypes: Dictionary<QName, Types> 
        // member pragmas are collected in order to do annotation checking
        memberPragmas: ResizeArray<Attribute.MemberPragma> 
    }

    static member Empty cliContext ncLut =
        { cliContext = cliContext
          ncEnv = ncLut
          nameToDecl = Dictionary() 
          userTypes = Dictionary() 
          memberPragmas = ResizeArray() }


module TypeCheckContext =
    let private tryGetSubProgramDeclAsPrototype = function
        | FunctionPrototype p -> Some p
        | SubProgramDecl d -> Some {
                FunctionPrototype.pos = d.pos
                isFunction = d.isFunction
                isSingleton = d.IsSingleton
                name = d.name
                inputs = d.inputs
                outputs = d.outputs
                returns = d.returns
                annotation = Attribute.FunctionPrototype.Empty
                allReferences = d.allReferences
            }
        | ParamDecl _
        | VarDecl _ 
        | ExternalVarDecl _ -> None

    let isConstVarDecl ctx (tml: TypedMemLoc) =
        // ensure it is a VarDecl (not a ParamDecl) and it is a compile time constant
        let qname = tml.QNamePrefix
        let declarable = ctx.nameToDecl.[qname]
        match declarable with
        | Declarable.VarDecl v -> v.IsConst
        | _ -> false

    /// A constant expression has only literals in its leaves
    /// but it need not be a literal as a whole
    let rec public isConstantExpr ctx expr =
        match expr.rhs with
        | IntConst _ 
        | BoolConst _
        | BitsConst _
        | NatConst _ 
        | FloatConst _
        | ResetConst -> true
        | StructConst fields -> 
            fields |> List.forall (snd >> isConstantExpr ctx)
        | ArrayConst fields -> 
            fields |> List.forall (snd >> isConstantExpr ctx)
        // locations
        | RhsCur tml
        | Prev tml -> isConstVarDecl ctx tml
        // call
        | FunCall _ -> false
        // type conversion
        | Convert (x, _, _) -> isConstantExpr ctx x
        // unary
        | Neg x 
        | Bnot x-> isConstantExpr ctx x
        // logical
        | Conj (x, y)
        | Disj (x, y)
        // bitwise
        | Band (x, y)
        | Bor (x, y)
        | Bxor (x, y)
        | Shl (x, y)
        | Shr (x, y)
        | Sshr (x, y)
        | Rotl (x, y)
        | Rotr (x, y)
        // relational
        | Les (x, y)
        | Leq (x, y)
        | Equ (x, y)
        // arithmetic
        | Add (x, y)
        | Sub (x, y)
        | Mul (x, y)
        | Div (x, y)
        | Mod (x, y) -> (isConstantExpr ctx x) && (isConstantExpr ctx y)

    // Getters ====================================================================
    let getTypeFromDecl (lut: TypeCheckContext) name pos =
        if lut.nameToDecl.ContainsKey(name) then
            let decl = lut.nameToDecl.[name]
            decl.AddReference pos |> ignore
            match decl with
            | Declarable.VarDecl v -> v.datatype |> Ok
            | Declarable.ExternalVarDecl v -> v.datatype |> Ok
            | Declarable.ParamDecl a -> a.datatype |> Ok
            | Declarable.SubProgramDecl _ 
            | Declarable.FunctionPrototype _ -> Error [IllegalAccessOfTypeInfo (name.ToString())]
        else
            Error [NotInLUTPrevError (name.ToString())]

    // Used also in causality analysis and code generation
    let rec getDatatypeFromTML (lut: TypeCheckContext) tml =
        match tml with
        | Loc qname -> 
            match lut.nameToDecl.[qname] with
            | Declarable.VarDecl v -> v.datatype 
            | Declarable.ExternalVarDecl v -> v.datatype
            | Declarable.ParamDecl a -> a.datatype
            | Declarable.SubProgramDecl _ 
            | Declarable.FunctionPrototype _ -> failwith "TML cannot point to a subprogram!"
        | FieldAccess (tml, ident) ->
            match getDatatypeFromTML lut tml with
            | ValueTypes (ValueTypes.StructType (_, name, fields))
            | ReferenceTypes (ReferenceTypes.StructType (_, name, fields)) ->
                fields
                |> List.find (fun f -> f.name.basicId = ident)
                |> (fun v -> v.datatype)
            | _ -> failwith "Field access on non-struct. Cannot happen!"
        | ArrayAccess (tml, _) -> 
            match getDatatypeFromTML lut tml with
            | ValueTypes (ArrayType(_, dty)) ->
                ValueTypes dty
            | _ -> failwith "Array access non non-array. Cannot happen!"

    let getSubProgDeclAsPrototype (lut: TypeCheckContext) pos name =
        if lut.nameToDecl.ContainsKey(name) then
            lut.nameToDecl.[name].AddReference pos |> ignore
            match tryGetSubProgramDeclAsPrototype lut.nameToDecl.[name] with
            | Some d -> Ok d
            | None -> Error [ExpectedSubProgDecl (pos, name.ToString())]
        else
            Error [NotInLUTPrevError (name.ToString())]


    // Setters ====================================================================
    let addDeclToLut (lut: TypeCheckContext) name decl =
        if lut.nameToDecl.ContainsKey(name) then
            failwith <| sprintf "Fatal error: tried to add the name \"%s\" to the lookup table twice. Probably name resolution works incorrectly!" (name.ToString())
        else
            lut.nameToDecl.Add(name, decl)


    let addTypeToLut (lut: TypeCheckContext) name typ =
        if lut.userTypes.ContainsKey(name) then
            failwith <| sprintf "Fatal error: tried to add the type name \"%s\" to the lookup table twice. Probably name resolution works incorrectly!" (name.ToString())
        else
            lut.userTypes.Add(name, typ)


    let addPragmaToLut (lut: TypeCheckContext) pragma =
        lut.memberPragmas.Add pragma


    // Testers ====================================================================
    let hasInclude (lut: TypeCheckContext) =
        Seq.exists (fun (mp: Attribute.MemberPragma) -> mp.IsInclude) lut.memberPragmas


    let hasCompile (lut: TypeCheckContext) =
        Seq.exists (fun (mp: Attribute.MemberPragma) -> mp.IsCompile) lut.memberPragmas
