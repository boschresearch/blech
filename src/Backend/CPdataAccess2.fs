// Copyright (c) 2020 - for information on the respective copyright owner
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
// This module has all the functions for
// reading and writing
// input, output, local, return variables and parameters
// in functions or activites
//=============================================================================

module Blech.Backend.CPdataAccess2

open Blech.Common.Range
open Blech.Common.PPrint

open Blech.Frontend
open Blech.Frontend.CommonTypes
open Blech.Frontend.PrettyPrint.DocPrint
open Blech.Frontend.BlechTypes
open Blech.Frontend.TypeCheckContext

open Blech.Backend
open Blech.Backend.Normalisation
open System.Collections.Generic


module AppName =

    let predefinedNames =
        [| "tick"; "init"; "printState" |]
    let private idxTick = 0
    let private idxInit = 1
    let private idxPrint = 2

    let private programName idx moduleName =
        QName.CreateProgramName moduleName predefinedNames.[idx]

    let tick = programName idxTick
    let init = programName idxInit
    let printState = programName idxPrint

type TemporalQualification =
    | Current
    | Previous

let private cpTabsize = 4

//=============================================================================
// Printing names
//=============================================================================

/// Produce an indented block of given sequence of statements (Docs)
let internal cpIndent = indent cpTabsize

let BLC = "blc" // do not add trailing "_" this is done by assembleName
let BLECH = BLC + "_blech"
let AUX = BLECH + "_aux"
let PREV = BLECH + "_prev"
let CTX = BLECH + "_ctx"

let private fromContext prefix =
    CTX + "->" + prefix

let private assembleName pref infixLst identifier =
    let infix = 
        let longId = String.concat "_" infixLst
        match longId with
        | "" -> ""
        | _ -> "_" + longId
    pref + infix + "_" + identifier
    |> txt

let private auxiliaryName name = assembleName AUX [] name.basicId
let private moduleLocalName name = assembleName BLC name.prefix name.basicId
let private autoName name = assembleName BLC [] name.basicId
let private globalName name = assembleName BLC (name.moduleName @ name.prefix) name.basicId
let private programName name = assembleName BLECH name.moduleName name.basicId
let private ctxName name = assembleName (fromContext BLC) [] name.basicId
let private externalPrev name = assembleName (fromContext PREV) [] name.basicId
let private internalPrev name = assembleName PREV [] name.basicId

[<DefaultAugmentation(false)>] // default Is* is on its way https://github.com/fsharp/fslang-suggestions/issues/222
                               // for the moment we do this as in https://stackoverflow.com/a/23665277/2289899
/// Represents information on how to render a Blech name to a C name
type CName =
    | Global of QName
    | ModuleLocal of QName
    | Auxiliary of QName
    | PrevInternal of QName
    | PrevExternal of QName
    | Auto of QName
    | CtxLocal of QName
    | ProgramName of QName // this category currently represents names of tick, init, print functions

    member this.QName =
        match this with
        | Global q
        | ModuleLocal q
        | Auxiliary q
        | PrevInternal q
        | PrevExternal q
        | Auto q
        | CtxLocal q 
        | ProgramName q -> q

    member this.Render =
        match this with
        | Global q -> globalName q
        | ModuleLocal q -> moduleLocalName q
        | Auxiliary q -> auxiliaryName q
        | PrevInternal q -> internalPrev q
        | PrevExternal q -> externalPrev q
        | Auto q -> autoName q
        | CtxLocal q -> ctxName q
        | ProgramName q -> programName q

    member this.IsAuxiliary =
        match this with
        | Auxiliary _ -> true
        | Global _ | ModuleLocal _
        | PrevInternal _ | PrevExternal _
        | Auto _ | CtxLocal _ 
        | ProgramName _ -> false


let private isInFunction tcc name =
    match name.prefix with
    | [] -> false
    | prefix ->
        let prefixAsName = QName.Create name.moduleName [] prefix.Head IdLabel.Static
        match tcc.nameToDecl.[prefixAsName] with
        | Declarable.SubProgramDecl spd ->
            spd.isFunction
        | _ -> failwithf "Cannot find code capsule for variable %s" (name.ToString())

let private isInActivity tcc name =
    match name.prefix with
    | [] -> false
    | prefix ->
        let prefixAsName = QName.Create name.moduleName [] prefix.Head IdLabel.Static
        match tcc.nameToDecl.[prefixAsName] with
        | Declarable.SubProgramDecl spd ->
            not spd.isFunction
        | _ -> failwithf "Cannot find code capsule for variable %s" (name.ToString())

/// Whenever a name has to be printed as C code this function does it
/// timepoint - None for procedures, types or Some (Current or Previous) for variable accesses
/// tcc - type check context
/// name - QName
// covers functions, activities, user types, variables
let cpName (timepointOpt: TemporalQualification option) tcc (name: QName) : CName =
    // Either a static QName of Function/Activity, user type or top level constant
    // or a const/param local inside a function/activity
    // TODO: do we want to lift these to the top level? Why not use C's statics inside functions?? fg 13.03.20
    let needsStaticName =
        name.IsStatic ||
        match tcc.nameToDecl.TryGetValue name with
        | true, Declarable.VarDecl v -> v.IsConst || v.IsParam
        | _,_ -> false

    if needsStaticName then
        if Array.contains name.basicId AppName.predefinedNames then
            // special case we have a generated "program name" such as init
            ProgramName name
        else
            // otherwise, decide here whether name is exported or not
            // for now always generate full global name
            Global name
    elif name.IsAuxiliary then
        // no prev on auxiliary variables
        assert timepointOpt.Equals (Some Current)
        // prepend aux_blc_
        Auxiliary name
    else
        assert name.IsDynamic
        assert (name.prefix <> [])
        let isParam =
            match tcc.nameToDecl.TryGetValue name with
            | true, Declarable.ParamDecl _ -> true
            | _ -> false

        if timepointOpt.Equals (Some Previous) then
            // Prev
            let isExternal =
                match tcc.nameToDecl.[name] with
                | Declarable.ExternalVarDecl _ -> true
                | _ -> false
            if isExternal then PrevExternal name
            else PrevInternal name
        elif isParam then
            // formal parameter
            Auto name
        elif isInFunction tcc name then
            // function local
            Auto name
        else
            // activity local
            assert isInActivity tcc name
            CtxLocal name

let renderCName tp tcc name = (cpName (Some tp) tcc name).Render

/// Shorthand for ppName None tcc name
/// >| Render
let cpStaticName = 
    cpName None TypeCheckContext.Empty
    >> (fun x -> x.Render)

/// Translates a primitive Blech type or a type name to a C type and returns a Doc representation thereof
let rec internal cpType typ =
    match typ with
    | ValueTypes Void -> txt "void"
    | ValueTypes BoolType -> txt "blc_bool"
    | ValueTypes (IntType size) ->
        match size with
        | Int8 -> txt "blc_int8"
        | Int16 -> txt "blc_int16"
        | Int32 -> txt "blc_int32"
        | Int64 -> txt "blc_int64"
    | ValueTypes (NatType size) ->
        match size with
        | Nat8 -> txt "blc_nat8"
        | Nat16 -> txt "blc_nat16"
        | Nat32 -> txt "blc_nat32"
        | Nat64 -> txt "blc_nat64"
    | ValueTypes (BitsType size) ->
           match size with
           | Bits8 -> txt "blc_bits8"
           | Bits16 -> txt "blc_bits16"
           | Bits32 -> txt "blc_bits32"
           | Bits64 -> txt "blc_bits64"
    | ValueTypes (FloatType size) ->
        match size with
        | FloatType.Float32 -> txt "blc_float32"
        | FloatType.Float64 -> txt "blc_float64"
    | ValueTypes (ValueTypes.StructType (_, typeName, _))
    | ReferenceTypes (ReferenceTypes.StructType (_, typeName,_)) ->
        txt "struct" <+> (cpStaticName typeName)
    | ValueTypes (ArrayType _) ->
        failwith "Do not call cpType on arrays. Use cpArrayDecl or cpArrayDeclDoc instead."
    | Any
    | AnyComposite 
    | AnyInt | AnyBits | AnyFloat -> failwith "Cannot print <Any> type."
    | ReferenceTypes _ -> failwith "Reference types not implemented yet. Cannot print them."

let rec internal sizeofMacro = function
| ValueTypes (ArrayType(size, elemTyp)) ->
    size |> string |> txt <+> txt "*" <+> sizeofMacro (ValueTypes elemTyp)
| x ->
    txt "sizeof" <^> parens (cpType x)


let private cpMemSetDoc typ lhsDoc =
    txt "memset"
    <^> dpCommaSeparatedInParens
        [ lhsDoc
          txt "0"
          sizeofMacro typ]
    <^> semi

   
type CBlob =
    | Name of CName
    | AddrOf of CBlob
    | ValueOf of CBlob

    member this.Render =
        match this with
        | Name d -> d.Render
        | AddrOf cap -> txt "(&" <^> cap.Render <^> txt ")"
        | ValueOf cap -> txt "(*" <^> cap.Render <^> txt ")"

    member this.Simplify =
        match this with
        | Name _
        | AddrOf (Name _)
        | ValueOf (Name _) -> this
        | AddrOf (ValueOf x) 
        | ValueOf (AddrOf x) -> x.Simplify
        | AddrOf (AddrOf x) -> (AddrOf x).Simplify // TODO: these two cases cannot happen as long as we do not have references
        | ValueOf (ValueOf x) -> (ValueOf x).Simplify

    member this.IsAuxiliary =
        match this with
        | Name n -> n.IsAuxiliary
        | AddrOf c 
        | ValueOf c -> c.IsAuxiliary


let getValueFromName timepoint tcc name : CBlob =
    let typeAndIsOutput =
        match tcc.nameToDecl.TryGetValue name with
        | true, Declarable.ParamDecl p -> Some p.datatype, p.isMutable
        | _ -> None, false
    let cName = cpName (Some timepoint) tcc name
    match typeAndIsOutput with
    | Some(ValueTypes (ValueTypes.StructType _)),_ ->
        ValueOf (Name cName)
    | Some typ, true when typ.IsPrimitive ->
        // primitive typed, output parameter
        ValueOf (Name cName)
    | _ ->
        Name cName

//=============================================================================
// Printing expressions
//=============================================================================

type RenderFun = CExpr list -> Doc
and CExpr =
    | Path of CPath
    | Value of Doc
    | ComplexExpr of RenderFun * CExpr list
    member this.Render =
        match this with
        | Path p -> p.Render
        | Value d -> d
        | ComplexExpr (f, c) -> f c

and CPath =
    | Loc of CBlob
    | FieldAccess of CPath * Doc
    | ArrayAccess of CPath * CExpr
    member this.Render =
        match this with
        | Loc cb -> cb.Render
        | FieldAccess (cp, f) -> cp.Render <^> txt "." <^> f
        | ArrayAccess (cp, e) -> cp.Render <^> txt "[" <^> e.Render <^> txt "]"

    member this.IsAuxiliary =
        match this with
        | Loc cb -> cb.IsAuxiliary
        | FieldAccess (cp, _) 
        | ArrayAccess (cp, _) -> cp.IsAuxiliary

    member this.PrependAddrOf =
        match this with
        | Loc blob -> AddrOf blob |> Loc
        | FieldAccess (cp, f) -> FieldAccess(cp.PrependAddrOf, f)
        | ArrayAccess (cp, i) -> ArrayAccess(cp.PrependAddrOf, i)


type PrereqExpression =
    {
        prereqStmts: Doc list
        cExpr: CExpr
    }
    member this.Render = this.cExpr.Render

let mkPrereqExpr p e =
    { PrereqExpression.prereqStmts = p
      cExpr = e }

let prereqExprBind f pe =
    let result = f pe.cExpr
    mkPrereqExpr
    <| pe.prereqStmts @ result.prereqStmts
    <| result.cExpr

let getCExpr pe = pe.cExpr
let getPrereq pe = pe.prereqStmts

let isExprAuxiliary pe =
    match getCExpr pe with
    | Path p -> p.IsAuxiliary
    // values or complex expression cannot be the result of creating an auxiliary variable
    | Value _ 
    | ComplexExpr _ -> false

type PrereqPath =
    {
        prereqStmts: Doc list
        path: CPath
    }
    member this.Render = this.path.Render
    member this.ToExpr =
        mkPrereqExpr
        <| this.prereqStmts
        <| Path this.path

let mkCPath p c =
    { prereqStmts = p
      path = c }


let rec cpTml timepoint tcc (tml: TypedMemLoc) : PrereqPath =
    match tml with
    | TypedMemLoc.Loc name -> 
        mkCPath
        <| []
        <| Loc (getValueFromName timepoint tcc name)
    | TypedMemLoc.FieldAccess (pref, field) ->
        let pp = cpTml timepoint tcc pref
        mkCPath
        <| pp.prereqStmts
        <| FieldAccess (pp.path, (txt field))
    | TypedMemLoc.ArrayAccess (pref, idx) ->
        let pp = cpTml timepoint tcc pref
        let suffix = cpExpr tcc idx
        mkCPath
        <| pp.prereqStmts @ suffix.prereqStmts
        <| ArrayAccess (pp.path, suffix.cExpr)

and private binExpr tcc s1 s2 infx =
    let re1 = cpExpr tcc s1
    let re2 = cpExpr tcc s2
    let render (rs: CExpr list) =
        rs.[0].Render
        |> (</>) <| txt infx
        |> (<+>) <| rs.[1].Render
        |> parens
    mkPrereqExpr
    <| (getPrereq re1 @ getPrereq re2)
    <| ComplexExpr (render, [getCExpr re1; getCExpr re2])

and private binConj tcc s1 s2 =
    let re1 = cpExpr tcc s1
    let re2 = cpExpr tcc s2
    match getPrereq re2 with
    | [] -> // this case is an optimisation
        let render (rs: CExpr list) =
            rs.[0].Render
            |> (</>) <| txt "&&"
            |> (<+>) <| rs.[1].Render
            |> parens
        mkPrereqExpr
        <| (getPrereq re1 @ getPrereq re2)
        <| ComplexExpr (render, [getCExpr re1; getCExpr re2])
    | _ -> 
        // make sure the second expression only get evaluated if
        // the first one was true
        let tmpVarIf =
            mkIndexedAuxQNameFrom "tmpVarIfStmt"
            |> TypedMemLoc.Loc
            |> cpTml Current tcc
            |> (fun x -> x.ToExpr)
        let renderedTmpVarIf = tmpVarIf.Render
        let initTmpVarIf =
            cpType (ValueTypes BoolType) <+> renderedTmpVarIf <+> txt "= 0" <^> semi
        let body =
            re2.prereqStmts @ [renderedTmpVarIf <+> txt "=" <+> re2.cExpr.Render <^> semi]
            |> dpBlock
        let ifWrapper = 
            txt "if (" <+> re1.cExpr.Render <+> txt ") {"
            <.> cpIndent body
            <.> txt "}"
        mkPrereqExpr
        <| (re1.prereqStmts @ [initTmpVarIf; ifWrapper])
        <| getCExpr tmpVarIf

and private binDisj tcc s1 s2 =
    let re1 = cpExpr tcc s1
    let re2 = cpExpr tcc s2
    match getPrereq re2 with
    | [] -> // this case is an optimisation
        let render (rs: CExpr list) =
            rs.[0].Render
            |> (</>) <| txt "||"
            |> (<+>) <| rs.[1].Render
            |> parens
        mkPrereqExpr
        <| (getPrereq re1 @ getPrereq re2)
        <| ComplexExpr (render, [getCExpr re1; getCExpr re2])
    | _ -> 
        // make sure the second expression only get evaluated if
        // the first one was false
        let tmpVarIf = 
            mkIndexedAuxQNameFrom "tmpVarIfStmt"
            |> TypedMemLoc.Loc
            |> cpTml Current tcc
            |> (fun x -> x.ToExpr)
        let initTmpVarIf =
            cpType (ValueTypes BoolType) <+> tmpVarIf.Render <+> txt "= 1" <^> semi
        let body =
            re2.prereqStmts @ [tmpVarIf.Render <+> txt "=" <+> re2.cExpr.Render <^> semi]
            |> dpBlock
        let ifWrapper = 
            txt "if (" <+> txt "!(" <^> re1.cExpr.Render <^> txt ")" <+> txt ") {"
            <.> cpIndent body
            <.> txt "}"
        mkPrereqExpr
        <| (re1.prereqStmts @ [initTmpVarIf; ifWrapper])
        <| getCExpr tmpVarIf

and cpExpr tcc expr : PrereqExpression =
    match expr.rhs with
    | RhsCur tml -> cpTml Current tcc tml |> (fun x -> x.ToExpr)
    | Prev tml -> cpTml Previous tcc tml |> (fun x -> x.ToExpr)
    // call
    | FunCall (whoToCall, inputs, outputs) ->
        let reIns = inputs |> List.map (cpInputArg tcc)
        let reOuts = outputs |> List.map (cpOutputArg tcc)
        let name = (cpStaticName whoToCall)
        let retType =
            match tcc.nameToDecl.[whoToCall].TryGetReturnType with
            | Some t -> t
            | None -> failwith "Expected to call a function but found something else!"
        
        if retType.IsPrimitive then
            // in case we call a function that returns a primitive value
            // rely on C return values
            let render (rs: CExpr list) =
                name <^> (rs |> List.map (fun x -> x.Render) |> dpCommaSeparatedInParens)
            mkPrereqExpr
            <| (reIns @ reOuts |> List.collect getPrereq)
            <| ComplexExpr (render, (reIns @ reOuts |> List.map getCExpr))
        else
            // in case we call a function that returns a non-primitive value
            // create a receiver passed as an extra parameter
            let lhsName = mkIndexedAuxQNameFrom "receiverVar"
            let lhsTyp = expr.typ
            let tmpDecl = cpArrayDeclDoc (auxiliaryName lhsName) lhsTyp <^> semi
            let v = 
                { 
                    VarDecl.pos = range0
                    name = lhsName
                    datatype = lhsTyp
                    mutability = Mutability.Variable
                    initValue = {rhs = NatConst Constants.Nat.Zero8; typ = ValueTypes (NatType Nat8); range = expr.range} // that is garbage
                    annotation = Attribute.VarDecl.Empty
                    allReferences = HashSet() 
                }
            TypeCheckContext.addDeclToLut tcc lhsName (Declarable.VarDecl v)
            let tmpLhs = LhsCur (TypedMemLoc.Loc lhsName)
            let tmpExpr = {lhs = tmpLhs; typ = lhsTyp; range = v.pos}
            let reReceiver = cpOutputArg tcc tmpExpr
            let funCall =
                name 
                <^> (reIns @ reOuts @ [reReceiver] |> List.map (getCExpr >> (fun x -> x.Render)) |> dpCommaSeparatedInParens) 
                <^> semi
            mkPrereqExpr
            <| ((reIns @ reOuts @ [reReceiver] |> List.collect getPrereq) @ [tmpDecl; funCall])
            <| getCExpr reReceiver

    // constants and literals
    | BoolConst b -> mkPrereqExpr [] (Value (if b then txt "1" else txt "0"))
    | IntConst i -> mkPrereqExpr [] (string i |> txt |> Value)
    | NatConst n -> mkPrereqExpr [] (string n |> txt |> Value)
    | BitsConst b -> mkPrereqExpr [] (string b |> txt |> Value)
    | FloatConst f -> mkPrereqExpr [] (string f |> txt |> Value)
    | ResetConst -> failwith "By now, the type checker should have substituted reset const by the type's default value."
    | StructConst assignments ->
        let resAssigns =
            assignments |> List.map (snd >> cpExpr tcc)
        let render (rs: CExpr list) =
            rs
            |> List.map (fun r -> r.Render)
            |> dpCommaSeparatedInBraces
        mkPrereqExpr
        <| (resAssigns |> List.collect getPrereq)
        <| ComplexExpr (render, (resAssigns |> List.map getCExpr))
    | ArrayConst elems ->    
        let resAssigns =
            elems |> List.map (snd >> cpExpr tcc)
        let render (rs: CExpr list) =
            rs
            |> List.map (fun r -> r.Render)
            |> dpCommaSeparatedInBraces
        mkPrereqExpr
        <| (resAssigns |> List.collect getPrereq)
        <| ComplexExpr (render, (resAssigns |> List.map getCExpr))
    //
    | Convert (subExpr, targetType, behaviour) ->   // TODO: Currently we generate a C cast for every behaviour, this will change with exceptions, fjg. 24.03.20
        let re = cpExpr tcc subExpr
        let rt = cpType targetType
        let render (rs: CExpr list) =
            parens rt <^> rs.[0].Render
        mkPrereqExpr
        <| re.prereqStmts
        <| ComplexExpr (render, [re.cExpr])
    // logical
    | Neg subExpr -> 
        let re = cpExpr tcc subExpr
        let render (rs: CExpr list) =
            txt "!" <^> parens rs.[0].Render
        mkPrereqExpr
        <| re.prereqStmts
        <| ComplexExpr (render, [re.cExpr])
    | Conj (s1, s2) -> binConj tcc s1 s2 
    | Disj (s1, s2) -> binDisj tcc s1 s2
    // bitwise
    | Bnot subExpr -> 
        let re = cpExpr tcc subExpr
        let render (rs: CExpr list) =
            (txt "~" <^> parens rs.[0].Render)
        mkPrereqExpr
        <| re.prereqStmts
        <| ComplexExpr (render, [re.cExpr])
    | Band (s1, s2) -> binExpr tcc s1 s2 "&"
    | Bor (s1, s2) -> binExpr tcc s1 s2 "|"
    | Bxor (s1, s2) -> binExpr tcc s1 s2 "^"
    | Shl (s1, s2) -> binExpr tcc s1 s2 "<<"
    | Shr (s1, s2) -> binExpr tcc s1 s2 ">>"
    | Sshr _ 
    | Rotl _
    | Rotr _ -> failwith "Advance shift operators '+>>', '<>>', '<<>' not implemented"
    // relational
    | Les (s1, s2) -> binExpr tcc s1 s2 "<"
    | Leq (s1, s2) -> binExpr tcc s1 s2 "<="
    | Equ (s1, s2) ->
        //assert (s1.typ = s2.typ) //fails for "x == 42" feature/bug?
        match s1.typ with //do not care about s2, since type checker ensures it is the same
        | ValueTypes BoolType
        | ValueTypes (IntType _)
        | ValueTypes (NatType _)
        | ValueTypes (BitsType _)
        | ValueTypes (FloatType _) ->
            binExpr tcc s1 s2 "=="
        | ValueTypes (ValueTypes.StructType _)
        | ValueTypes (ValueTypes.ArrayType _) ->
            let re1 = cpInputArg tcc s1
            let re2 = cpInputArg tcc s2
            let length = sizeofMacro s1.typ
            let render (rs: CExpr list) =
                txt "0 == memcmp" <^> dpCommaSeparatedInParens [rs.[0].Render; rs.[1].Render; length]
            mkPrereqExpr
            <| (getPrereq re1 @ getPrereq re2)
            <| ComplexExpr (render, [getCExpr re1; getCExpr re2])
        | ValueTypes Void
        | Any
        | AnyComposite 
        | AnyInt 
        | AnyBits
        | AnyFloat -> failwith "Error in type checker. Trying to compare void or not fully typed expressions."
        | ReferenceTypes _ -> failwith "Comparing reference types not implemented."
    // arithmetic
    | Add (s1, s2) -> binExpr tcc s1 s2 "+"
    | Sub (s1, s2) -> binExpr tcc s1 s2 "-"
    | Mul (s1, s2) -> binExpr tcc s1 s2 "*"
    | Div (s1, s2) -> binExpr tcc s1 s2 "/"
    | Mod (s1, s2) -> binExpr tcc s1 s2 "%"

and cpInputArg tcc expr : PrereqExpression = 
    // if expr is a structured literal, make a new name for it
    let singleArgLocation: PrereqExpression = makeTmpForComplexConst tcc expr
    match expr.typ with
    | ValueTypes (ValueTypes.StructType _) -> //when isExprAuxiliary singleArgLocation ->
        // if auxiliary struct, then prepend &
        let cExpr = 
            match getCExpr singleArgLocation with
            | Path cPath -> cPath.PrependAddrOf |> Path
            | x -> x // impossible due to isExprAuxiliary check above
        mkPrereqExpr
        <| getPrereq singleArgLocation
        <| cExpr
    | _ -> singleArgLocation

and cpOutputArg tcc expr : PrereqExpression = 
    // unless array, prepend &
    let pe = cpLexpr tcc expr
    match expr.typ with
    | ValueTypes (ValueTypes.ArrayType _) -> pe
    | _ ->
        let cExpr = 
            match getCExpr pe with
            | Path cPath -> cPath.PrependAddrOf |> Path
            | x -> x // impossible, a lhs cannot be a complex expression or just a value
        mkPrereqExpr
        <| getPrereq pe
        <| cExpr

and cpLexpr tcc expr : PrereqExpression =
    match expr.lhs with
    | Wildcard -> failwith "Lhs cannot be a wildcard at this stage."
    | LhsCur tml -> cpTml Current tcc tml |> (fun x -> x.ToExpr)
    | LhsNext _ -> failwith "render next locations not implemented yet."

and cpArrayDeclDoc name typ =
    let rec cpRecArrayDeclDoc n t =
        match t with
        | ValueTypes (ArrayType(size, elemTyp)) ->
            let nameAndType, length = cpRecArrayDeclDoc n (ValueTypes elemTyp)
            nameAndType, brackets (size |> string |> txt) <^> length
        | _ ->
            cpType t <+> n, empty
    cpRecArrayDeclDoc name typ ||> (<^>)

/// Given an expression that is a struct or array literal,
/// or a name that stands for a literal (const variable),
/// or a function call returning such data type,
/// this function creates code that stores the literal value
/// in a temporary variable and returns a name that can be 
/// used as an argument for a function or activity.
and makeTmpForComplexConst tcc (expr: TypedRhs) : PrereqExpression =
    let copyContents =
        let lhsName = mkIndexedAuxQNameFrom "tmpLiteral"
        let lhsTyp = expr.typ
        let tmpDecl = cpArrayDeclDoc (auxiliaryName lhsName) lhsTyp <^> semi
        let init =
            match expr.typ with
            | ValueTypes (ValueTypes.StructType _) ->
                //let cname = cpName (Some Current) tcc lhsName
            
                //let v = 
                //    { 
                //        VarDecl.pos = range0
                //        name = lhsName
                //        datatype = lhsTyp
                //        mutability = Mutability.Variable
                //        initValue = {rhs = NatConst Constants.Nat.Zero8; typ = ValueTypes (NatType Nat8); range = expr.range} // that is garbage
                //        annotation = Attribute.VarDecl.Empty
                //        allReferences = HashSet() 
                //    }
                //TypeCheckContext.addDeclToLut tcc lhsName (Declarable.VarDecl v)
                cpMemSetDoc expr.typ (txt "&" <^> auxiliaryName lhsName)
            | ValueTypes (ValueTypes.ArrayType _) ->
                cpMemSetDoc expr.typ (auxiliaryName lhsName)
            | _ ->
                empty //failwith "Cannot not do anything about rhs which are simple value constants" // This has been checked somewhere else
        let lhs = {lhs = LhsCur (TypedMemLoc.Loc lhsName); typ = expr.typ; range = range0}
        let assignments = 
            normaliseAssign tcc (range0, lhs, expr)
            |> List.map (function 
                | Stmt.Assign(_, lhs, rhs) -> 
                    let rightRE = cpExpr tcc rhs
                    let leftRE = cpLexpr tcc lhs
                    let assignment = leftRE.Render <+> txt "=" <+> rightRE.Render <^> semi
                    rightRE.prereqStmts @ leftRE.prereqStmts @ [assignment] |> dpBlock
                | _ -> failwith "Must be an assignment here!") // not nice
        mkPrereqExpr
        <| (tmpDecl :: init :: assignments)
        <| (TypedMemLoc.Loc lhsName |> cpTml Current tcc |> (fun x -> x.ToExpr.cExpr))

    match expr.typ with
    | ValueTypes (ValueTypes.StructType _)
    | ValueTypes (ValueTypes.ArrayType _) ->
        match expr.rhs with
        | StructConst _ 
        | ArrayConst _ ->
            copyContents
        | RhsCur tml when isConstVarDecl tcc tml ->        
            copyContents
        //| FunCall (whoToCall,inputs,outputs) ->
            // this case is handled inside cpExpr, it will automatically
            // generate a tmp variable for storing a complex return value
        | _ ->
            // nothing to do for param/let/var names
            // other cases of expression cannot appear here
            cpExpr tcc expr
    | _ ->
        // nothing to do for simple types
        cpExpr tcc expr
    


//=============================================================================
// Printing statements
//=============================================================================
//type RenderedStmt =
//    {
//        prereqStmts: Doc list
//        renderedStmt: Doc
//    }
//    member this.Render =
//        this.prereqStmts @ [this.renderedStmt]
//        |> dpBlock

let nullify tcc lhs =
    // ensure we get a pointer to the data, means no * for structs
    let lhsDoc = (cpOutputArg tcc lhs).Render
    cpMemSetDoc lhs.typ lhsDoc

let mkRenderedStmt p r =
    p @ [r]
    |> dpBlock

//let RenderedStmtFromExpr (re: PrereqExpression) =
//    mkRenderedStmt
//    <| re.prereqStmts
//    <| (re.cExpr.Render <^> semi)


let rec cpAssign tcc left right =
    let leftRE = cpLexpr tcc left
    let rightRE = cpExpr tcc right
    let directAssigment = 
        mkRenderedStmt
        <| leftRE.prereqStmts @ rightRE.prereqStmts
        <| (leftRE.cExpr.Render <+> txt "=" <+> rightRE.cExpr.Render <^> semi)
    match left.typ with
    | ValueTypes (ValueTypes.ArrayType _) ->
        // memcopy arrays
        let memcpy =
            txt "memcpy"
            <^> dpCommaSeparatedInParens
                [ leftRE.cExpr.Render
                  rightRE.cExpr.Render
                  sizeofMacro right.typ ]
            <^> semi
        mkRenderedStmt
        <| leftRE.prereqStmts @ rightRE.prereqStmts
        <| memcpy
    | ValueTypes (ValueTypes.StructType _) -> // assign structs
        let norm =
            normaliseAssign tcc (left.Range, left, right)
            |> List.map (function 
                | Stmt.Assign(_, lhs, rhs) -> cpAssign tcc lhs rhs
                | _ -> failwith "Must be an assignment here!") // not nice
        
        match right.rhs with
        | StructConst _
        | ArrayConst _ -> //when isLiteral right ->
            let reinit = nullify tcc left
            reinit :: norm |> dpBlock
        | _ -> // x = y needs no rewriting, assign directly
            directAssigment 
    | ValueTypes Void 
    | ValueTypes BoolType 
    | ValueTypes (IntType _)
    | ValueTypes (NatType _)
    | ValueTypes (BitsType _) 
    | ValueTypes (FloatType _) ->
        // assign primitives
        directAssigment
    | ReferenceTypes _ -> failwith "Code generation for reference types not implemented."
    | Any // used for wildcard
    | AnyComposite // compound literals
    | AnyInt // used for untyped integer literals
    | AnyBits // of Bits // used for untyped bits literals 
    | AnyFloat -> failwith "Any types must have been eliminated by the type checker. This is a bug."


let cpFunctionCall tcc whoToCall inputs outputs =
    let pe =
        {rhs = FunCall (whoToCall, inputs, outputs); typ = ValueTypes Void; range = range0}
        |> cpExpr tcc
    mkRenderedStmt
    <| pe.prereqStmts
    <| (pe.cExpr.Render <^> semi)


/// Create a Doc for an activity call
/// tcc - type check context
/// pcName - string, the calling thread's program counter name (used as field name in activity context)
/// whoToCall - QName of callee
/// inputs
/// outputs
/// receiverVar - optional TypedLhs (r = run A...)
/// termRetcodeVarName - QName of the variable that stores the termination information
let cpActivityCall tcc pcName whoToCall inputs outputs receiverVar termRetcodeVarName =
    let renderedCalleeName = (cpStaticName whoToCall)
    let renderedInputs = inputs |> List.map (cpInputArg tcc)
    let renderedOutputs = outputs |> List.map (cpOutputArg tcc)
    let subctx = txt "&blc_blech_ctx->" <^> txt pcName <^> txt "_" <^> renderedCalleeName
    let renderedRetvarOpt =
        receiverVar
        |> Option.map (cpOutputArg tcc)
    let actCall = 
        [
            renderedInputs |> List.map (getCExpr >> (fun x -> x.Render))
            renderedOutputs |> List.map (getCExpr >> (fun x -> x.Render))
            [subctx]
            renderedRetvarOpt |> Option.toList |> List.map (getCExpr >> (fun x -> x.Render))
        ]
        |> List.concat
        |> dpCommaSeparatedInParens
        |> (<^>) renderedCalleeName
    let prereqStmts =
        [
            renderedInputs |> List.collect getPrereq
            renderedOutputs |> List.collect getPrereq
            renderedRetvarOpt |> Option.toList |> List.collect getPrereq 
        ]
        |> List.concat
    let actCallStmt = (cpName (Some Current) tcc termRetcodeVarName).Render <+> txt "=" <+> actCall <^> semi
    mkRenderedStmt prereqStmts actCallStmt

/// Sets non array typed prev variables to their types default
/// TODO: make work with all types
let cpAssignDefaultPrevInActivity ctx qname =
    let tml = TypedMemLoc.Loc qname
    let dty = getDatatypeFromTML ctx tml
    let prevname = (cpName (Some Previous) ctx qname).Render
    let {prereqStmts=prereq; cExpr=value} = cpExpr ctx {rhs = RhsCur tml; typ = dty; range = range0} //range0, since this does not exist in the Blech source code
    prereq
    @ [prevname <+> txt "=" <+> value.Render <^> semi]
    |> dpBlock
           
let cpAssignPrevInActivity tcc qname =
    let tml = TypedMemLoc.Loc qname
    let dty = getDatatypeFromTML tcc tml
    let prevname = (cpName (Some Previous) tcc qname).Render
    let initvalue = (getValueFromName Current tcc qname).Render
    
    match dty with
    | ValueTypes (ArrayType _) ->
        let declare = cpArrayDeclDoc prevname dty <^> semi
        let memcpy =
            txt "memcpy"
            <+> dpCommaSeparatedInParens
                [ prevname
                  initvalue
                  sizeofMacro dty ]
            <^> semi
        declare <..> memcpy
    | _ ->
        cpType dty 
        <+> prevname <+> txt "=" 
        <+> initvalue <^> semi
        
//TODO eliminate these
let internal cpDeref o = txt "*" <^> o
let internal cpRefto o = txt "&" <^> o