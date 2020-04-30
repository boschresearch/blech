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

type TemporalQualification =
    | Current
    | Previous

let private cpTabsize = 4

//=============================================================================
// Printing names
//=============================================================================

/// Produce an indented block of given sequence of statements (Docs)
let internal cpIndent = indent cpTabsize

let private BLC = "blc" // do not add trailing "_" this is done by assembleName
let private AUX = "aux_" + BLC
let private PREV = "prev_" + BLC
let private CTX = "blc_blech_ctx"

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

let private prevName tcc name =
    let isExternal =
        match tcc.nameToDecl.[name] with
        | Declarable.ExternalVarDecl _ -> true
        | _ -> false
    if isExternal then
        // prev external variable
        assembleName
        <| fromContext PREV
        <| []
        <| name.basicId
    else
        // prev internal variable
        assembleName PREV [] name.basicId

let private moduleLocalName name = assembleName BLC name.prefix name.basicId
let private autoName name = assembleName BLC [] name.basicId
let private globalName name = assembleName BLC (name.moduleName @ name.prefix) name.basicId

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
let cpName (timepointOpt: TemporalQualification option) tcc (name: QName) =
    // Either a static QName of Function/Activity, user type or top level constant
    // or a const/param local inside a function/activity
    // TODO: do we want to lift these to the top level? Why not use C's statics inside functions?? fg 13.03.20
    let needsStaticName =
        name.IsStatic ||
        match tcc.nameToDecl.TryGetValue name with
        | true, Declarable.VarDecl v -> v.IsConst || v.IsParam
        | _,_ -> false

    if needsStaticName then
        // decide here whether name is exported or not
        // for now always generate full global name
        globalName name
    elif name.IsAuxiliary then
        // no prev on auxiliary variables
        assert timepointOpt.Equals (Some Current)
        // prepend aux_blc_
        auxiliaryName name
    else
        assert name.IsDynamic
        assert (name.prefix <> [])
        let isParam =
            match tcc.nameToDecl.TryGetValue name with
            | true, Declarable.ParamDecl _ -> true
            | _ -> false

        if timepointOpt.Equals (Some Previous) then
            // Prev
            prevName tcc name
        elif isParam then
            // formal parameter
            autoName name
        elif isInFunction tcc name then
            // function local
            autoName name
        else
            // activity local
            assert isInActivity tcc name
            assembleName
            <| fromContext BLC
            <| []
            <| name.basicId

/// Shorthand for ppName None tcc name
let cpStaticName = cpName None TypeCheckContext.Empty           

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
        txt "struct" <+> cpStaticName typeName
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
    
type CAccessPath =
    | Name of Doc
    | AddrOf of CAccessPath
    | ValueOf of CAccessPath

    member this.ToDoc =
        match this with
        | Name d -> d
        | AddrOf cap -> txt "&(" <^> cap.ToDoc <^> txt ")"
        | ValueOf cap -> txt "*(" <^> cap.ToDoc <^> txt ")"

    member this.Simplify =
        match this with
        | Name _
        | AddrOf (Name _)
        | ValueOf (Name _) -> this
        | AddrOf (ValueOf x) 
        | ValueOf (AddrOf x) -> x.Simplify
        | AddrOf (AddrOf x) -> (AddrOf x).Simplify // TODO: these two cases cannot happen as long as we do not have references
        | ValueOf (ValueOf x) -> (ValueOf x).Simplify

let cpCAccessPath (cap: CAccessPath) = cap.ToDoc

let getValueFromName timepoint tcc name : CAccessPath =
    let typeAndIsOutput =
        match tcc.nameToDecl.TryGetValue name with
        | true, Declarable.ParamDecl p -> Some p.datatype, p.isMutable
        | _ -> None, false
    let nameDoc = cpName (Some timepoint) tcc name
    match typeAndIsOutput with
    | Some typ, true ->
        if typ.IsPrimitive then
            // primitive typed, output parameter
            ValueOf (Name nameDoc)
        // TODO: elif struct type then also *<name>?
        else
            Name nameDoc
    | _ ->
        Name nameDoc

//=============================================================================
// Printing expressions
//=============================================================================

type RenderedExpression =
    {
        prereqStmts: Doc list
        renderedExpr: Doc
    }

let mkRenderedExpr p e =
    { RenderedExpression.prereqStmts = p
      renderedExpr = e }

let RenderedExprBind f re =
    let result = f re.renderedExpr
    mkRenderedExpr
    <| re.prereqStmts @ result.prereqStmts
    <| result.renderedExpr

    
let GetRenderedExpr re = re.renderedExpr
let GetPrereq re = re.prereqStmts


let rec cpTml timepoint tcc tml : RenderedExpression =
    match tml with
    | Loc name ->
        mkRenderedExpr
        <| []
        <| (getValueFromName timepoint tcc name).ToDoc
    | FieldAccess (pref, field) ->
        let f d = 
            mkRenderedExpr
            <| []
            <| (d <^> txt "." <^> txt field)
        cpTml timepoint tcc pref
        |> RenderedExprBind f
    | ArrayAccess (pref, idx) ->
        let f d =
            let renderedIdx = cpExpr tcc idx
            mkRenderedExpr
            <| renderedIdx.prereqStmts
            <| (d <^> txt "[" <^> renderedIdx.renderedExpr <^> txt "]")
        cpTml timepoint tcc pref
        |> RenderedExprBind f

and private binExpr tcc s1 s2 infx =
    let re1 = cpExpr tcc s1
    let re2 = cpExpr tcc s2
    let processedExpr =
        GetRenderedExpr re1
        |> (</>) <| txt infx
        |> (<+>) <| GetRenderedExpr re2
        |> parens
    mkRenderedExpr
    <| (GetPrereq re1 @ GetPrereq re2)
    <| processedExpr

and private binConj tcc s1 s2 =
    let re1 = cpExpr tcc s1
    let re2 = cpExpr tcc s2
    match GetPrereq re2 with
    | [] -> 
        let processedExpr =
            GetRenderedExpr re1
            |> (</>) <| txt "&&"
            |> (<+>) <| GetRenderedExpr re2
            |> parens
        mkRenderedExpr
        <| (GetPrereq re1 @ GetPrereq re2)
        <| processedExpr
    | _ -> 
        // make sure the second expression only get evaluated if
        // the first one was true
        let tmpVarIf = mkIndexedAuxQNameFrom "tmpVarIfStmt" |> auxiliaryName
        let initTmpVarIf =
            cpType (ValueTypes BoolType) <+> tmpVarIf <+> txt "= 0" <^> semi
        let body =
            re2.prereqStmts @ [tmpVarIf <+> txt "=" <+> re2.renderedExpr <^> semi]
            |> dpBlock
        let ifWrapper = 
            txt "if (" <+> re1.renderedExpr <+> txt ") {"
            <.> cpIndent body
            <.> txt "}"
        mkRenderedExpr
        <| (re1.prereqStmts @ [initTmpVarIf; ifWrapper])
        <| tmpVarIf

and private binDisj tcc s1 s2 =
    let re1 = cpExpr tcc s1
    let re2 = cpExpr tcc s2
    match GetPrereq re2 with
    | [] -> 
        let processedExpr =
            GetRenderedExpr re1
            |> (</>) <| txt "||"
            |> (<+>) <| GetRenderedExpr re2
            |> parens
        mkRenderedExpr
        <| (GetPrereq re1 @ GetPrereq re2)
        <| processedExpr
    | _ -> 
        // make sure the second expression only get evaluated if
        // the first one was false
        let tmpVarIf = mkIndexedAuxQNameFrom "tmpVarIfStmt" |> auxiliaryName
        let initTmpVarIf =
            cpType (ValueTypes BoolType) <+> tmpVarIf <+> txt "= 1" <^> semi
        let body =
            re2.prereqStmts @ [tmpVarIf <+> txt "=" <+> re2.renderedExpr <^> semi]
            |> dpBlock
        let ifWrapper = 
            txt "if (" <+> txt "!(" <^> re1.renderedExpr <^> txt ")" <+> txt ") {"
            <.> cpIndent body
            <.> txt "}"
        mkRenderedExpr
        <| (re1.prereqStmts @ [initTmpVarIf; ifWrapper])
        <| tmpVarIf

and cpExpr tcc expr : RenderedExpression =
    match expr.rhs with
    | RhsCur tml -> cpTml Current tcc tml //|> RenderedExprFromTML
    | Prev tml -> cpTml Previous tcc tml //|> RenderedExprFromTML
    // call
    | FunCall (whoToCall, inputs, outputs) ->
        let reIns = inputs |> List.map (cpInputArg tcc)
        let reOuts = outputs |> List.map (cpOutputArg tcc)
        let name = cpStaticName whoToCall
        let retType =
            match tcc.nameToDecl.[whoToCall].TryGetReturnType with
            | Some t -> t
            | None -> failwith "Expected to call a function but found something else!"
        // in case we call a function that returns a non-primitive value
        if retType.IsPrimitive then
            mkRenderedExpr
            <| (reIns @ reOuts |> List.collect GetPrereq)
            <| (name <^> (reIns @ reOuts |> List.map GetRenderedExpr |> dpCommaSeparatedInBraces))
        else
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
            let tmpLhs = LhsCur (Loc lhsName)
            let tmpExpr = {lhs = tmpLhs; typ = lhsTyp; range = v.pos}
            let reReceiver = cpOutputArg tcc tmpExpr
            let funCall =
                name 
                <^> (reIns @ reOuts @ [reReceiver] |> List.map GetRenderedExpr |> dpCommaSeparatedInBraces) 
                <^> semi
            mkRenderedExpr
            <| ((reIns @ reOuts @ [reReceiver] |> List.collect GetPrereq) @ [tmpDecl; funCall])
            <| GetRenderedExpr reReceiver

    // constants and literals
    | BoolConst b -> mkRenderedExpr [] (if b then txt "1" else txt "0")
    | IntConst i -> mkRenderedExpr [] (txt <| string i)
    | NatConst n -> mkRenderedExpr [] (txt <| string n)
    | BitsConst b -> mkRenderedExpr [] (txt <| string b)
    | FloatConst f -> mkRenderedExpr [] (txt <| string f)
    | ResetConst -> failwith "By now, the type checker should have substituted reset const by the type's default value."
    | StructConst assignments ->
        let resAssigns =
            assignments |> List.map (snd >> cpExpr tcc)
        mkRenderedExpr
        <| (resAssigns |> List.collect GetPrereq)
        <| (resAssigns |> List.map GetRenderedExpr |> dpCommaSeparatedInBraces)
    | ArrayConst elems ->    
        let resAssigns =
            elems |> List.map (snd >> cpExpr tcc)
        mkRenderedExpr
        <| (resAssigns |> List.collect GetPrereq)
        <| (resAssigns |> List.map GetRenderedExpr |> dpCommaSeparatedInBraces)
    //
    | Convert (subExpr, targetType, behaviour) ->   // TODO: Currently we generate a C cast for every behaviour, this will change with exceptions, fjg. 24.03.20
        let re = cpExpr tcc subExpr
        let rt = cpType targetType
        mkRenderedExpr
        <| re.prereqStmts
        <| (parens rt <^> re.renderedExpr)
    // logical
    | Neg subExpr -> 
        let re = cpExpr tcc subExpr
        mkRenderedExpr
        <| re.prereqStmts
        <| (txt "!" <^> parens re.renderedExpr)
    | Conj(s1, s2) -> binConj tcc s1 s2 
    | Disj(s1, s2) -> binDisj tcc s1 s2
    // bitwise
    | Bnot subExpr -> 
        let re = cpExpr tcc subExpr
        mkRenderedExpr
        <| re.prereqStmts
        <| (txt "~" <^> parens re.renderedExpr)
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
        assert (s1.typ = s2.typ)
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
            mkRenderedExpr
            <| (GetPrereq re1 @ GetPrereq re2)
            <| (txt "0 == memcmp" <^> dpCommaSeparatedInParens [GetRenderedExpr re1; GetRenderedExpr re2; length])
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

and cpInputArg tcc expr : RenderedExpression = 
    // if expr is a structured literal, make a new name for it
    cpExpr tcc expr // FIXME: dummy code
    //TODO:
    //match makeTmpForComplexConst tcc expr with
    //| E re -> re
    //| T rtml ->
    //    match expr.typ with
    //    | ValueTypes (ValueTypes.StructType _) ->
    //        // if struct, then prepend &
    //        let newTML = (AddrOf rtml.renderedTML).Simplify
    //        mkRenderedTML rtml.prereqStmts newTML
    //        |> RenderedExprFromTML
    //    | _ -> 
    //        RenderedExprFromTML rtml

and cpOutputArg tcc expr : RenderedExpression = 
    // unless array, prepend &
    cpLexpr tcc expr // FIXME: dummy code
    // TODO:
    //let re = cpLexpr tcc expr
    //match expr.typ with
    //| ValueTypes (ValueTypes.ArrayType _) -> re
    //| _ ->
    //    let newTML = (AddrOf re.)
    //    {
    //        prereqStmts = re.prereqStmts
    //        renderedTML = AddrOf re.renderedTML
    //    }

and cpLexpr tcc expr : RenderedExpression =
    match expr.lhs with
    | Wildcard -> failwith "Lhs cannot be a wildcard at this stage."
    | LhsCur tml -> cpTml Current tcc tml //|> RenderedExprFromTML
    | LhsNext _ -> failwith "render next locations not implemented yet."

and internal cpArrayDeclDoc name typ =
    let rec cpRecArrayDeclDoc n t =
        match t with
        | ValueTypes (ArrayType(size, elemTyp)) ->
            let nameAndType, length = cpRecArrayDeclDoc n (ValueTypes elemTyp)
            nameAndType, brackets (size |> string |> txt) <^> length
        | _ ->
            cpType t <+> n, empty
    cpRecArrayDeclDoc name typ ||> (<^>)

// TODO: old garbage?
/// Given an expression that is a struct or array literal,
/// or a name that stands for a literal (const variable),
/// or a function call returning such data type,
/// this function creates code that stores the literal value
/// in a temporary variable and returns a name that can be 
/// used as an argument for a function or activity.
//let makeTmpForComplexConst tcc (expr: TypedRhs) : TMLorExpr =
//    //let myPrint (lhs: LhsStructure) =
//    //    let rec myPrintTml =
//    //        function
//    //        | Loc qname -> qname.ToString()
//    //        | TypedMemLoc.FieldAccess (tml, ident) -> myPrintTml tml + "." + ident
//    //        | TypedMemLoc.ArrayAccess (tml, idx) -> sprintf "%s[%s]" (myPrintTml tml) (idx.ToString())

//    //    match lhs with
//    //    | Wildcard -> txt "_"
//    //    | LhsCur t -> t.ToDoc
//    //    | LhsNext t -> txt "next" <+> t.ToDoc

//    let cpMemSetDoc typ lhsDoc =
//        txt "memset"
//        <^> dpCommaSeparatedInParens
//            [ lhsDoc
//              txt "0"
//              sizeofMacro typ]
//        <^> semi
    
//    let copyContents =
//        let lhsName = mkIndexedAuxQNameFrom "tmpLiteral"
//        let cname = cpName (Some Current) tcc lhsName
//        match expr.typ with
//        | ValueTypes (ValueTypes.StructType _) ->
//            let tmpDecl = cpType expr.typ <+> cname <^> semi // <+> txt "=" <+> literal
//            let init = cpMemSetDoc expr.typ (txt "&" <^> cname)
//            let lhs = {lhs = LhsCur (Loc lhsName); typ = expr.typ; range = range0}
//            let assignments = 
//                normaliseAssign tcc (range0, lhs, expr)
//                |> List.map (function 
//                    | Stmt.Assign(_, lhs, rhs) -> 
//                        let rightRE = cpExpr tcc rhs
//                        let leftRE = cpLexpr tcc lhs
//                        let assignment = leftRE.renderedExpr <+> txt "=" <+> rightRE.renderedExpr <^> semi
//                        rightRE.prereqStmts @ leftRE.prereqStmts @ [assignment] |> dpBlock
//                    | _ -> failwith "Must be an assignment here!") // not nice
//            mkRenderedTML (tmpDecl :: init :: assignments) (Name cname)
//            |> T
//        | ValueTypes (ValueTypes.ArrayType _) ->
//            let tmpDecl = cpArrayDeclDoc cname expr.typ <^> semi
//            let init = cpMemSetDoc expr.typ cname
//            let lhs = {lhs = LhsCur (Loc lhsName); typ = expr.typ; range = range0}
//            let assignments = 
//                normaliseAssign tcc (range0, lhs, expr)
//                |> List.map (function 
//                    | Stmt.Assign(_, lhs, rhs) ->
//                        let rightRE = cpExpr tcc rhs
//                        let leftRE = cpLexpr tcc lhs
//                        let assignment = leftRE.renderedExpr <+> txt "=" <+> rightRE.renderedExpr <^> semi
//                        rightRE.prereqStmts @ [assignment] |> dpBlock
//                    | _ -> failwith "Must be an assignment here!") // not nice
//            mkRenderedTML (tmpDecl :: init :: assignments) (Name cname) // the only difference to above
//            |> T
//        | _ -> failwith "Cannot not do anything about rhs which are simple value constants" // This has been checked somewhere else

//    let storeIntermediateValue whoToCall inputs outputs=
//        let lhsName = mkIndexedAuxQNameFrom "tmpLiteral"
//        let cname = cpName (Some Current) tcc lhsName
//        let funCall = cpFunctionCall tcc whoToCall inputs outputs

    
//    match expr.typ with
//    | ValueTypes (ValueTypes.StructType _)
//    | ValueTypes (ValueTypes.ArrayType _) ->
//        match expr.rhs with
//        | StructConst _ 
//        | ArrayConst _ ->
//            copyContents
//        | RhsCur tml when isConstVarDecl tcc tml ->        
//            copyContents
//        | FunCall (whoToCall,inputs,outputs) ->
//            storeIntermediateValue whoToCall inputs outputs
//        | _ ->
//            // nothing to do for param/let/var names
//            // other cases of expression cannot appear here
//            E <| cpExpr tcc expr
//    | _ ->
//        // nothing to do for simple types
//        E <| cpExpr tcc expr
    


//=============================================================================
// Printing statements
//=============================================================================
type RenderedStmt =
    {
        prereqStmts: Doc list
        renderedStmt: Doc
    }

let mkRenderedStmt p r =
    { prereqStmts = p
      renderedStmt = r }

let RenderedStmtFromExpr (re: RenderedExpression) =
    mkRenderedStmt
    <| re.prereqStmts
    <| re.renderedExpr


let cpAssign tcc left right : RenderedStmt =
    let leftRE = cpLexpr tcc left
    let rightRE = cpExpr tcc right
    let directAssigment = 
        mkRenderedStmt
        <| leftRE.prereqStmts @ rightRE.prereqStmts
        <| (leftRE.renderedExpr <+> txt "=" <+> rightRE.renderedExpr <^> semi)
    match left.typ with
    | ValueTypes (ValueTypes.ArrayType _) ->
        // memcopy arrays
        let memcpy =
            txt "memcpy"
            <^> dpCommaSeparatedInParens
                [ leftRE.renderedExpr
                  rightRE.renderedExpr
                  sizeofMacro right.typ ]
            <^> semi
        mkRenderedStmt
        <| leftRE.prereqStmts @ rightRE.prereqStmts
        <| memcpy
    | ValueTypes (ValueTypes.StructType _) ->
        // assign structs
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


let cpFunctionCall tcc whoToCall inputs outputs : RenderedStmt =
    {rhs = FunCall (whoToCall, inputs, outputs); typ = ValueTypes Void; range = range0}
    |> cpExpr tcc
    |> RenderedStmtFromExpr


/// Create a Doc for an activity call
/// tcc - type check context
/// pcName - string, the calling thread's program counter name (used as field name in activity context)
/// whoToCall - QName of callee
/// inputs
/// outputs
/// receiverVar - optional TypedLhs (r = run A...)
/// termRetcodeVarName - QName of the variable that stores the termination information
let cpActivityCall tcc pcName whoToCall inputs outputs receiverVar isDummy termRetcodeVarName : RenderedStmt =
    let renderedCalleeName = cpStaticName whoToCall
    let renderedInputs = inputs |> List.map (cpInputArg tcc)
    let renderedOutputs = outputs |> List.map (cpOutputArg tcc)
    let subctx = txt "&blc_blech_ctx->" <^> txt pcName <^> txt "_" <^> renderedCalleeName
    let renderedRetvarOpt =
        receiverVar
        |> Option.map (cpOutputArg tcc)
    let actCall = 
        [
            renderedInputs |> List.map GetRenderedExpr
            renderedOutputs |> List.map GetRenderedExpr
            [subctx]
            renderedRetvarOpt |> Option.toList |> List.map GetRenderedExpr
        ]
        |> List.concat
        |> dpCommaSeparatedInParens
        |> (<^>) renderedCalleeName
    let prereqStmts =
        [
            renderedInputs |> List.collect GetPrereq
            renderedOutputs |> List.collect GetPrereq
            renderedRetvarOpt |> Option.toList |> List.collect GetPrereq 
        ]
        |> List.concat
    let actCallStmt = (cpName (Some Current) tcc termRetcodeVarName) <+> txt "=" <+> actCall <^> semi
    mkRenderedStmt prereqStmts actCallStmt


           
           
        
