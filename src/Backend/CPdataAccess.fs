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
// -----------------------------------------------------
//
// SCODE Zwicky Box (considering only value datatypes, only simple and structs)
// +----------------------------------------------------
// | SubProgKind     || Function | Activity
// | DeclKind        || Local | InputParam | OutputParam | Constant
// | Usage           || Lhs | Rhs | OutputArg | InputArg
// | ElementDatatype || ValueSimple | ValueStruct | ValueArray
// | AccessKind      || Direct | FieldAccess | ArrayAccess
// | Timepoint       || Current | Previous
// +----------------------------------------------------
// 234 out of 576 combinations are valid
// 
// Depending on these properties we determine first if we need the contents
// or the address thereof. 
//
// Then we determine how to access the contents (either directly by name or
// dereferencing the container's name).
// 
//=============================================================================

module Blech.Backend.CPdataAccess

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


//=============================================================================
// General pretty printing functions
//=============================================================================

let private cpTabsize = 4

/// Produce an indented block of given sequence of statements (Docs)
let internal cpIndent = indent cpTabsize


// TODO: QName prefix needs module part and scope part, local names need not contain the module part
// For the moment the module part is an empty string (""), see namechecking function enterModuleScope
// All names names get the 'blc_' prefix
// fjg, 17.01.19
// let private  qnameToCName name prefix =
//    name.prefix @ [name.basicId]
//    |> String.concat "_" 
//    |> (+) prefix

let private longIdentifierToCName (longid: LongIdentifier) =
    String.concat "_" longid


/// Returns a string representation of a qualified name to be used for local c identifiers
let private translateQnameToLocalName name =
    let localScopes = List.tail name.prefix  // Remove name of first scope, keep anonymous scopes
    let cPref = longIdentifierToCName localScopes 
    if cPref = "" then
        sprintf "blc_%s" name.basicId
    else
        sprintf "blc_%s_%s" cPref name.basicId
    
/// Returns a string representation of a qualified name to be used for static (file local) c identifiers
let private translateQnameToStaticName name =
    let cPref = longIdentifierToCName name.prefix
    if cPref = "" then
        sprintf "blc_%s" name.basicId
    else
        sprintf "blc_%s_%s" cPref name.basicId

/// Returns a string representation of a qualified name to be used for global c identifiers    
let private translateQnameToGlobalName name =
    let cModName = longIdentifierToCName name.moduleName
    let cPref = longIdentifierToCName name.prefix
    if "" = cPref then
        sprintf "blc_%s_%s" cModName name.basicId
    else
        sprintf "blc_%s_%s_%s" cModName cPref name.basicId
   
/// Returns a string representation of a qualified name to be used for local generated c identifiers
/// TODO: add module names for generated names for the next code generation, fjg 26.01.19
let internal translateQnameToGeneratedName name =
    let cPref = longIdentifierToCName name.prefix
    if "" = cPref then
        name.basicId
    else
        sprintf "%s_%s" cPref name.basicId


/// Returns a string representation of a qualified name to be used for program name c identifiers: tick, init and printState
let internal translateQnameToProgramName name =
    assert (name.prefix.Length = 0)
    let cModName = longIdentifierToCName name.moduleName
    sprintf "blc_blech_%s_%s" cModName name.basicId // 'blech' is a reserved id and cannot conflict with any blech module name


//=============================================================================
// Atomic language elements
//=============================================================================

/// Translate Qname to Doc

let internal ppName (name: QName) = 
    match name.label with
    | Auxiliary ->
        txt <| translateQnameToGeneratedName name
    | Static ->
        txt <| translateQnameToStaticName name 
    | Dynamic ->
        txt <| translateQnameToLocalName name

        
let internal ppNameInActivity (name: QName) =
    match name.label with
    | Auxiliary ->
        txt <| translateQnameToGeneratedName name
    | Static
    | Dynamic ->
        txt <| translateQnameToStaticName name 

let internal ppNameInGlobalCall = ppNameInActivity

let internal ppStaticName (name: QName) =
    txt <| translateQnameToStaticName name

let internal ppGlobalName (name:QName) =
    txt <| translateQnameToGlobalName name

// TODO: generated something like blc_prev_<prefix>_<basicid> for next and prev names, fjg 26.01.19
//let private ppNextName name = txt "next_" <^> ppNameInActivity name
let internal ppPrevName name = txt "prev_" <^> ppNameInActivity name

let internal cpDeref o = txt "*" <^> o
let internal cpRefto o = txt "&" <^> o

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
    | ValueTypes (UintType size) ->
        match size with
        | Uint8 -> txt "blc_uint8"
        | Uint16 -> txt "blc_uint16"
        | Uint32 -> txt "blc_uint32"
        | Uint64 -> txt "blc_uint64"
    | ValueTypes (FloatType size) ->
        match size with
        | FloatPrecision.Single -> txt "blc_float32"
        | FloatPrecision.Double -> txt "blc_float64"
    | ValueTypes (ValueTypes.StructType (_, typeName, _))
    | ReferenceTypes (ReferenceTypes.StructType (_, typeName,_)) ->
        txt "struct" <+> ppGlobalName typeName
    | ValueTypes (ArrayType _) ->
        failwith "Do not call cpType on arrays. Use cpArrayDecl or cpArrayDeclDoc instead."
    | AnyComposite 
    | AnyInt _ -> failwith "Cannot print <Any> type."
    | ReferenceTypes _ -> failwith "Reference types not implemented yet. Cannot print them."


let rec internal sizeofMacro = function
    | ValueTypes (ArrayType(size, elemTyp)) ->
        size |> string |> txt <+> txt "*" <+> sizeofMacro (ValueTypes elemTyp)
    | x ->
        txt "sizeof" <^> parens (cpType x)


/// Return the type signature where the first Array access is decayed into a pointer, e.g.
/// blc_int8 (*)[5] for an integer ?-by-5 matrix.
let private cpArrayAsPointerDeclDoc typ =
    let mutable madeStar = false
    let rec cpRecArrayAsPtr t =
        match t with
        | ValueTypes (ArrayType(size, elemTyp)) ->
            if not madeStar then
                madeStar <- true
                let nameAndType, length = cpRecArrayAsPtr (ValueTypes elemTyp)
                nameAndType, txt "(*)" <^> length
            else
                let nameAndType, length = cpRecArrayAsPtr (ValueTypes elemTyp)
                nameAndType, brackets (size |> string |> txt) <^> length
        | _ ->
            cpType t, empty
    cpRecArrayAsPtr typ ||> (<^>)

let internal cpArrayDeclDoc name typ =
    let rec cpRecArrayDeclDoc n t =
        match t with
        | ValueTypes (ArrayType(size, elemTyp)) ->
            let nameAndType, length = cpRecArrayDeclDoc n (ValueTypes elemTyp)
            nameAndType, brackets (size |> string |> txt) <^> length
        | _ ->
            cpType t <+> n, empty
    cpRecArrayDeclDoc name typ ||> (<^>)

let internal cpArrayDecl name typ = cpArrayDeclDoc (ppName name) typ

let internal cpArrayDeclInActivity name typ = cpArrayDeclDoc (ppNameInActivity name) typ

type TransExpr =
    | Done of Doc
    | Orig of TypedRhs

//=============================================================================    
// Scode Dimensions
//=============================================================================
type private DeclKind =
    | InputParam
    | OutputParam
    | Local
    | Constant
    | StaticParameter // not in SCODE analysis

type private SubProgKind =
    | Function
    | Activity

type private Usage =
    | Lhs
    | Rhs
    | InputArg
    | OutputArg

type private ElementDatatype =
    | ValueSimple
    | ValueStruct
    | ValueArray

type private AccessKind =
    | Direct
    | FieldAccess
    | ArrayAccess

type private TemporalQualification =
    | Current
    | Previous 

/// Given the current Compilation, search its iface in order to determine
/// whether we have a input, local or output
let private getDeclKind (ctx: TranslationContext) (name:TypedMemLoc) =
    try
        match ctx.tcc.nameToDecl.[name.QNamePrefix] with
        | Declarable.ParamDecl p ->
            if p.isMutable then OutputParam
            else InputParam
        | Declarable.VarDecl v when v.mutability.Equals Mutability.CompileTimeConstant -> Constant
        | Declarable.VarDecl v when v.mutability.Equals Mutability.StaticParameter -> StaticParameter
        | Declarable.VarDecl _ -> Local
        | Declarable.ExternalVarDecl v when v.mutability.Equals Mutability.CompileTimeConstant -> Constant
        | Declarable.ExternalVarDecl v when v.mutability.Equals Mutability.StaticParameter -> StaticParameter
        | Declarable.ExternalVarDecl _ -> Local
        | Declarable.SubProgramDecl _
        | Declarable.FunctionPrototype _ -> failwith "The name of a sub program cannot appear where data is expected." 
    with
    | _ -> failwith <| sprintf "Trying to print an unknown name %s. Global variable?" (name.ToString())

let rec private trimToFirstAccess (tml: TypedMemLoc) =
    match tml with
    | Loc _
    | TypedMemLoc.FieldAccess (Loc _, _)
    | TypedMemLoc.ArrayAccess (Loc _, _) -> tml
    | TypedMemLoc.FieldAccess (subtml, _)
    | TypedMemLoc.ArrayAccess (subtml, _) -> trimToFirstAccess subtml

let private getElementDatatype (ctx: TranslationContext) (tml:TypedMemLoc) =
    let tml = trimToFirstAccess tml
    match getDatatypeFromTML ctx.tcc tml with
    | AnyComposite 
    | AnyInt _ -> failwith "Impossible. Cannot print a data item of type Any."
    | ValueTypes (ValueTypes.Void) -> failwith "Impossible. Cannot print a data item of type void."
    | ValueTypes (ValueTypes.BoolType)
    | ValueTypes (ValueTypes.FloatType _)
    | ValueTypes (ValueTypes.IntType _)
    | ValueTypes (ValueTypes.UintType _) -> ValueSimple
    | ValueTypes (ValueTypes.StructType _) -> ValueStruct
    | ValueTypes (ValueTypes.ArrayType _) -> ValueArray
    | ReferenceTypes _ -> failwith "Reference types not yet implemented."

let private getAccessKind (tml:TypedMemLoc) =
    let tml = trimToFirstAccess tml
    match tml with
    | Loc _ -> Direct
    | TypedMemLoc.FieldAccess _ -> AccessKind.FieldAccess
    | TypedMemLoc.ArrayAccess _ -> AccessKind.ArrayAccess

let private needAddress subProgKind usage timepoint (ctx: TranslationContext) (tml:TypedMemLoc) =
    let declKind = getDeclKind ctx tml
    let elemType = getElementDatatype ctx tml
    let accessKind = getAccessKind tml
    if usage.Equals OutputArg && timepoint.Equals Current then
        if accessKind.Equals Direct && subProgKind.Equals Function && declKind.Equals Local then
            if elemType.Equals ValueSimple || elemType.Equals ValueStruct then
                true
            else
                false
        elif (accessKind.Equals FieldAccess || accessKind.Equals ArrayAccess) && (declKind.Equals Local || declKind.Equals OutputParam) then
            if elemType.Equals ValueSimple || elemType.Equals ValueStruct then
                true
            else
                false
        else
            false
    elif usage.Equals InputArg && elemType.Equals ValueStruct then
        if timepoint.Equals Previous && subProgKind.Equals Activity && declKind.Equals Local then
            true
        elif timepoint.Equals Current then 
            if accessKind.Equals FieldAccess || accessKind.Equals ArrayAccess then
                true
            elif accessKind.Equals Direct && subProgKind.Equals Function && declKind.Equals Local then
                true
            elif accessKind.Equals Direct && declKind.Equals Constant then
                true
            elif accessKind.Equals Direct && declKind.Equals StaticParameter then // not in SCODE analysis
                true
            else
                false
        else
            false
    else
        false

let private needDereferencing subProgKind usage timepoint ctx tml =
    let declKind = getDeclKind ctx tml
    let elemType = getElementDatatype ctx tml
    let accessKind = getAccessKind tml
    
    match timepoint with
    | Current ->
        match declKind with
        | InputParam -> 
            if accessKind.Equals Direct && elemType.Equals ValueStruct && usage.Equals Rhs then
                true
            elif accessKind.Equals FieldAccess && (usage.Equals Rhs || usage.Equals InputArg) then
                true
            else
                false
        | Local ->
            if subProgKind.Equals Activity && accessKind.Equals FieldAccess then
                true
            elif subProgKind.Equals Activity && accessKind.Equals Direct && (usage.Equals Lhs || usage.Equals Rhs) && (elemType.Equals ValueSimple || elemType.Equals ValueStruct) then
                true
            elif subProgKind.Equals Activity && accessKind.Equals Direct && usage.Equals InputArg && elemType.Equals ValueSimple then
                true
            else
                false
        | OutputParam ->
            if accessKind.Equals FieldAccess then
                true
            elif accessKind.Equals Direct && (usage.Equals Lhs || usage.Equals Rhs) && (elemType.Equals ValueSimple || elemType.Equals ValueStruct) then
                true
            elif accessKind.Equals Direct && usage.Equals InputArg && elemType.Equals ValueSimple then
                true
            else
                false
        | Constant
        | StaticParameter -> // not in SCODE analysis
            false
    | Previous ->
        false

type private TmlSubstructure =
    | FieldAccess of string
    | IndexAccess of TypedRhs

let rec private decomposeTml = function
    | Loc name -> name, []
    | TypedMemLoc.FieldAccess (subtml, fa) ->
        let name, accesses = decomposeTml subtml
        name, accesses @ [TmlSubstructure.FieldAccess fa]
    | TypedMemLoc.ArrayAccess (subtml, idx) ->
        let name, accesses = decomposeTml subtml
        name, accesses @ [TmlSubstructure.IndexAccess idx]


let private moveConstFields ctx container fields =
    if isConstVarDecl ctx.tcc (Loc container) then
        let rec moveConstField (tml: TypedMemLoc) fs =
            match fs with
            | [] -> tml, []
            | FieldAccess ident :: rest -> moveConstField (tml.AddFieldAccess ident) rest
            | IndexAccess idx :: rest ->
                match idx.rhs with
                | IntConst _ -> moveConstField (tml.AddArrayAccess idx) rest
                | _ -> tml, fs
        moveConstField (Loc container) fields
    else
        (Loc container), fields

let rec private appendDotFields inFunction ctx fields =
    let renderSubStr = function
        | FieldAccess ident -> [] , txt "." <^> txt ident
        | IndexAccess trhs ->
            cpExpr inFunction ctx trhs
            |> fun (f, s) -> f, s |> brackets
    List.fold (fun acc field -> 
        let prereqStmts, renderedSubExpr = renderSubStr field
        fst acc @ prereqStmts,
        snd acc <^> renderedSubExpr
        ) ([],empty) fields

/// Given an expression that is a struct or array literal,
/// or a name that stands for a literal (const variable),
/// this function creates code that stores the literal value
/// in a temporary variable and returns a name that can be 
/// used to call function or activity.
and makeTmpForComplexConst inFunction ctx (expr: TypedRhs) =
    let myPrint (lhs: LhsStructure) =
        let rec myPrintTml =
            function
            | Loc qname -> qname.ToString()
            | TypedMemLoc.FieldAccess (tml, ident) -> myPrintTml tml + "." + ident
            | TypedMemLoc.ArrayAccess (tml, idx) -> sprintf "%s[%s]" (myPrintTml tml) (idx.ToString())

        match lhs with
        | Wildcard -> txt "_"
        | LhsCur t -> t.ToDoc
        | LhsNext t -> txt "next" <+> t.ToDoc
    
    let copyContents =
        let lhsName = mkIndexedAuxQNameFrom "tmpLiteral"
        let cname = ppName lhsName
        // is it complex?
        match expr.typ with
        | ValueTypes (ValueTypes.StructType _) ->
            let tmpDecl = cpType expr.typ <+> cname <^> semi // <+> txt "=" <+> literal
            let init = cpMemSetDoc expr.typ (cname |> cpRefto)
            let lhs = {lhs = LhsCur (Loc lhsName); typ = expr.typ; range = range0}
            let assignments = 
                normaliseAssign ctx.tcc (range0, lhs, expr)
                |> List.map (function 
                    | Stmt.Assign(_, lhs, rhs) -> 
                        let prereqStmts, processedRhs = cpExpr inFunction ctx rhs
                        let assignment = myPrint lhs.lhs <+> txt "=" <+> processedRhs <^> semi
                        prereqStmts @ [assignment] |> dpBlock
                    | _ -> failwith "Must be an assignment here!") // not nice
            
            tmpDecl :: init :: assignments, Done (cname |> cpRefto)    
            
        | ValueTypes (ValueTypes.ArrayType _) ->
            let tmpDecl = cpArrayDeclDoc cname expr.typ <^> semi
            let init = cpMemSetDoc expr.typ cname
            let lhs = {lhs = LhsCur (Loc lhsName); typ = expr.typ; range = range0}
            let assignments = 
                normaliseAssign ctx.tcc (range0, lhs, expr)
                |> List.map (function 
                    | Stmt.Assign(_, lhs, rhs) -> 
                        let prereqStmts, processedRhs = cpExpr inFunction ctx rhs
                        let assignment = myPrint lhs.lhs <+> txt "=" <+> processedRhs <^> semi
                        prereqStmts @ [assignment] |> dpBlock
                    | _ -> failwith "Must be an assignment here!") // not nice
            tmpDecl :: init :: assignments, Done cname // the only difference to above
        | _ -> [], Orig expr // do not do anything about rhs which are simple value constants
    match expr.rhs with
    | StructConst _ 
    | ArrayConst _ ->
        copyContents
    | RhsCur tml when isConstVarDecl ctx.tcc tml ->        
        copyContents
    | _ -> [], Orig expr
// factored out name printing decision to a callback function
and private cpRenderData subProgKind usage timepoint (ctx: TranslationContext) (tml:TypedMemLoc) renderName =
    let getAddr doc =
        if needAddress subProgKind usage timepoint ctx tml then
            doc |> parens |> cpRefto
        else
            doc
    let dereference doc =
        if needDereferencing subProgKind usage timepoint ctx tml then
            doc |> cpDeref |> parens
        else
            doc
    
    let isTmlOnlyName = function | Loc _ -> true | _ -> false
    // need generation of tmp vars for constants here according to SCODE analysis
    if not (isTmlOnlyName tml) && isConstVarDecl ctx.tcc tml then
        // make tmp var
        let container, fields = decomposeTml tml
        let container, fields = moveConstFields ctx container fields
        let prereq, tmpvar =
            makeTmpForComplexConst (subProgKind.Equals SubProgKind.Function) ctx { rhs = RhsCur container; typ = getDatatypeFromTML ctx.tcc container; range = range0}
            |> function
                | x, Done y -> x, y
                | x, Orig e -> 
                    let foo, bar = cpExpr (subProgKind.Equals SubProgKind.Function) ctx e
                    x @ foo, bar
        let prereq2, accesses = appendDotFields (subProgKind.Equals SubProgKind.Function) ctx fields
        prereq @ prereq2, tmpvar <^> accesses |> getAddr
    else
        // render name as usual
        let container, fields = decomposeTml tml
        // hack: if prev on external variable, change name and treat as a current local variable
        let timepoint, container =
            let isExternal = 
                match ctx.tcc.nameToDecl.[container] with
                | Declarable.ExternalVarDecl _ -> true
                | _ -> false
            if timepoint.Equals Previous && isExternal then
                Current, {container with basicId = "prev_" + container.basicId}
            else
                timepoint, container
        // end hack
    
        let prefix = 
            match timepoint with
            | Current ->
                renderName container
            | Previous-> 
                ppPrevName container  // always a local in an activity
            |> dereference
        let prereq, accesses = appendDotFields (subProgKind.Equals SubProgKind.Function) ctx fields
        let result = 
            prefix <^> accesses
            |> getAddr
        prereq, result
           

and private decomposeRhs = function
    | RhsCur name -> Current, name
    | Prev name -> Previous, name
    | _ -> failwith "cpRhsIn... expects an atomic expression"

and private decomposeLhs = function
    | LhsCur name -> Current, name
    | LhsNext _ -> failwith "render next locations not implemented yet."
    | Wildcard -> failwith "Lhs cannot be a wildcard at this stage."

and private selectNameRendererInActivity ctx tml =
    match getDeclKind ctx tml with
    | DeclKind.Local 
    | DeclKind.Constant 
    | DeclKind.StaticParameter when tml.QNamePrefix.IsDynamic -> ppNameInActivity // see comment on dynamic names in local constants in CommonTypes.fs:38
    | _ -> ppName
    
and private selectNameRendererInFunction ctx tml =
    match getDeclKind ctx tml with
    | DeclKind.Constant
    | DeclKind.StaticParameter when tml.QNamePrefix.IsDynamic -> translateQnameToStaticName >> txt // see comment on dynamic names in local constants in CommonTypes.fs:38
    | _ -> ppName

and cpRhsInFunction ctx rhs =
    let timepoint, tml = decomposeRhs rhs
    let renderName = selectNameRendererInFunction ctx tml
    cpRenderData SubProgKind.Function Usage.Rhs timepoint ctx tml renderName

and cpRhsInActivity ctx rhs =
    let timepoint, tml = decomposeRhs rhs
    let renderName = selectNameRendererInActivity ctx tml
    let declaration = ctx.tcc.nameToDecl.[tml.QNamePrefix]
    // if external && let/var && current, treat like local in activity
    let isExtCurVar =
        match declaration with
        | Declarable.VarDecl _ 
        | Declarable.ParamDecl _ -> // regular variable in activity
            false
        | Declarable.ExternalVarDecl v -> // special case, external variable
            match v.mutability with
            | Mutability.CompileTimeConstant
            | Mutability.StaticParameter -> // treat external constants the same as above
                false
            | Mutability.Variable
            | Mutability.Immutable -> // treat extern let/var in activity like a local in a function
                match timepoint with
                | Current -> true
                | _ -> false
        | FunctionPrototype _
        | SubProgramDecl _ 
            -> failwith "Tried printing a variable, got something else."
    let subProgKind =
        if isExtCurVar then SubProgKind.Function
        else SubProgKind.Activity
    cpRenderData subProgKind Usage.Rhs timepoint ctx tml renderName
    

and cpLhsInFunction ctx lhs =
    let timepoint, tml = decomposeLhs lhs
    let renderName = selectNameRendererInFunction ctx tml
    cpRenderData SubProgKind.Function Usage.Lhs timepoint ctx tml renderName

and cpLhsInActivity ctx lhs =
    let timepoint, tml = decomposeLhs lhs
    let renderName = selectNameRendererInActivity ctx tml
    // if external && let/var && current, treat like local in activity
    let declaration = ctx.tcc.nameToDecl.[tml.QNamePrefix]
    let isExtCurVar =
        match declaration with
        | Declarable.VarDecl _ 
        | Declarable.ParamDecl _ -> // regular variable in activity
            false
        | Declarable.ExternalVarDecl v -> // special case, external variable
            match v.mutability with
            | Mutability.CompileTimeConstant
            | Mutability.StaticParameter -> // treat external constants the same as above
                false
            | Mutability.Variable
            | Mutability.Immutable -> // treat extern let/var in activity like a local in a function
                match timepoint with
                | Current -> true
                | _ -> false
        | FunctionPrototype _
        | SubProgramDecl _ 
            -> failwith "Tried printing a variable, got something else."
    let subProgKind =
        if isExtCurVar then SubProgKind.Function
        else SubProgKind.Activity
    cpRenderData subProgKind Usage.Lhs timepoint ctx tml renderName

and cpOutputArgInFunction ctx lhs =
    let timepoint, tml = decomposeLhs lhs
    let renderName = selectNameRendererInFunction ctx tml
    cpRenderData SubProgKind.Function Usage.OutputArg timepoint ctx tml renderName

and cpOutputArgInActivity ctx lhs =
    let timepoint, tml = decomposeLhs lhs
    let renderName = selectNameRendererInActivity ctx tml
    // if external && let/var && current, treat like local in activity
    let declaration = ctx.tcc.nameToDecl.[tml.QNamePrefix]
    let isExtCurVar =
        match declaration with
        | Declarable.VarDecl _ 
        | Declarable.ParamDecl _ -> // regular variable in activity
            false
        | Declarable.ExternalVarDecl v -> // special case, external variable
            match v.mutability with
            | Mutability.CompileTimeConstant
            | Mutability.StaticParameter -> // treat external constants the same as above
                false
            | Mutability.Variable
            | Mutability.Immutable -> // treat extern let/var in activity like a local in a function
                match timepoint with
                | Current -> true
                | _ -> false
        | FunctionPrototype _
        | SubProgramDecl _ 
            -> failwith "Tried printing a variable, got something else."
    let subProgKind =
        if isExtCurVar then SubProgKind.Function
        else SubProgKind.Activity
    cpRenderData subProgKind Usage.OutputArg timepoint ctx tml renderName

and cpMemCpyArr inFunction ctx lhs (rhs: TypedRhs) =
    let prereqLhs, processedLhs = 
        if lhs = Wildcard then
            [], empty
        else
            if inFunction then cpOutputArgInFunction ctx lhs
            else cpOutputArgInActivity ctx lhs
    let prereqStmts, processedRhs = cpExpr inFunction ctx rhs
    let memcpy =
        txt "memcpy"
        <^> dpCommaSeparatedInParens
            [ processedLhs // TODO: this is a bug when processedLhs is empty
              processedRhs
              sizeofMacro rhs.typ]
        <^> semi
            
    prereqLhs @ prereqStmts @ [memcpy]
    |> dpBlock

and cpMemCpyDoc inFunction ctx lhs rhsDoc =
    if lhs.lhs = Wildcard then empty
    else
        let prereqLhs, processedLhs = 
            if inFunction then cpOutputArgInFunction ctx lhs.lhs
            else cpOutputArgInActivity ctx lhs.lhs
        let memcpy =
            txt "memcpy"
            <^> dpCommaSeparatedInParens
                [ processedLhs // TODO: this is a bug when processedLhs is empty
                  rhsDoc
                  sizeofMacro lhs.typ]
            <^> semi
        prereqLhs @ [memcpy]
        |> dpBlock            

and cpMemSet inFunction ctx lhs =
    match lhs.lhs with
    | Wildcard -> empty // nothing to do, any result would be thrown away
    | LhsCur _
    | LhsNext _ ->
        let prereqLhs, processedLhs = 
            if inFunction then cpOutputArgInFunction ctx lhs.lhs
            else cpOutputArgInActivity ctx lhs.lhs
        let memset =
            txt "memset"
            <^> dpCommaSeparatedInParens
                [ processedLhs
                  txt "0"
                  sizeofMacro lhs.typ]
            <^> semi
            
        prereqLhs @ [memset]
        |> dpBlock

and cpMemSetDoc typ lhsDoc =
    txt "memset"
    <^> dpCommaSeparatedInParens
        [ lhsDoc
          txt "0"
          sizeofMacro typ]
    <^> semi

and cpInputArgInSubprogram inFunction ctx (rhs: TypedRhs) : Doc list * Doc =
    let subProgKind = if inFunction then SubProgKind.Function else SubProgKind.Activity
    let maybeConstCast =
        match rhs.typ with
        | ValueTypes (ArrayType (size, dty)) ->
            txt "const" <+> cpArrayAsPointerDeclDoc rhs.typ
            |> parens
        | _ -> empty
    match rhs.rhs with
    // simple literals
    | BoolConst b -> [], if b then txt "1" else txt "0"
    | IntConst i -> [], txt <| string i
    | FloatConst f -> [], f.ToDoc
    | RhsCur _
    | Prev _ -> // the prev case cannot be matched inside a function context!
        let timepoint, tml = decomposeRhs rhs.rhs
        let renderName = if inFunction then ppName else selectNameRendererInActivity ctx tml
        let prereqStmts, renderedTml = cpRenderData subProgKind Usage.InputArg timepoint ctx tml renderName
        prereqStmts, maybeConstCast <+> renderedTml
    | _ -> cpExpr inFunction ctx rhs


//=============================================================================
// Expressions
//=============================================================================
and private cpNeg e = txt "!" <^> parens e

and private binExpr inFunction ctx s1 s2 infx =
    let prereqStmts1, normalisedS1 = cpExpr inFunction ctx s1
    let prereqStmts2, normalisedS2 = cpExpr inFunction ctx s2
    let processedExpr =
        normalisedS1
        |> (</>) <| txt infx
        |> (<+>) <| normalisedS2
        |> parens
    List.concat [prereqStmts1; prereqStmts2], processedExpr

and private binConj inFunction ctx s1 s2 =
    let prereqStmts1, normalisedS1 = cpExpr inFunction ctx s1
    let prereqStmts2, normalisedS2 = cpExpr inFunction ctx s2
    match prereqStmts2 with
    | [] -> 
        let processedExpr =
            normalisedS1
            |> (</>) <| txt "&&"
            |> (<+>) <| normalisedS2
            |> parens
        prereqStmts1, processedExpr
    | _ -> 
        let tmpVarIf = mkIndexedAuxQNameFrom "tmpVarIfStmt"
        let initTmpVarIf =
            cpType (ValueTypes BoolType) <+> ppName tmpVarIf <+> txt "= 0" <^> semi
        let body =
            prereqStmts2 @ [ppName tmpVarIf <+> txt "=" <+> normalisedS2 <^> semi]
            |> dpBlock
        let ifWrapper = 
            txt "if (" <+> normalisedS1 <+> txt ") {"
            <.> cpIndent body
            <.> txt "}"
        let prereqStmts =
            prereqStmts1 @ [initTmpVarIf; ifWrapper]
        prereqStmts, ppName tmpVarIf

and private binDisj inFunction ctx s1 s2 =
    let prereqStmts1, normalisedS1 = cpExpr inFunction ctx s1
    let prereqStmts2, normalisedS2 = cpExpr inFunction ctx s2
    match prereqStmts2 with
    | [] -> 
        let processedExpr =
            normalisedS1
            |> (</>) <| txt "||"
            |> (<+>) <| normalisedS2
            |> parens
        prereqStmts1, processedExpr
    | _ -> 
        let tmpVarIf = mkIndexedAuxQNameFrom "tmpVarIfStmt" 
        let initTmpVarIf =
            cpType (ValueTypes BoolType) <+> ppName tmpVarIf <+> txt "= 1" <^> semi
        let body =
            prereqStmts2 @ [ppName tmpVarIf <+> txt "=" <+> normalisedS2 <^> semi]
            |> dpBlock
        let ifWrapper = 
            txt "if (" <+> txt "!(" <^> normalisedS1 <^> txt ")" <+> txt ") {"
            <.> cpIndent body
            <.> txt "}"
        let prereqStmts =
            prereqStmts1 @ [initTmpVarIf; ifWrapper]
        prereqStmts, ppName tmpVarIf

/// Convert expressions into Doc
/// Ensures that function calls with struct literals in their input list are
/// converted to function calls on precomputed structure variables.
// The result propagates recursively.
// Even if the resulting data type is simple, the expression producing that
// may contain sub-expressions that need to be rewritten, e.g.
// g( f({i=8}) ), where f is simply boolean but its argument needs to be rewritten
and private cpExpr inFunction ctx expr =
    match expr.rhs with
    | RhsCur name -> 
        (ctx, (RhsCur name)) ||> if inFunction then cpRhsInFunction else cpRhsInActivity
    | Prev name ->
        // ensure the compilation of the current activity has this location in its varsToPrev list
        //addToPrev curComp expr
        (ctx, (Prev name)) ||> if inFunction then cpRhsInFunction else cpRhsInActivity
    // we "normalise" function calls in-place whenever the inputs contain struct literals
    | FunCall (whoToCall, inputs, outputs) ->
        let nameDoc, retType = 
            match ctx.tcc.nameToDecl.[whoToCall] with
            | Declarable.FunctionPrototype fp when fp.isDirectCCall -> ppName whoToCall, fp.returns
            | Declarable.FunctionPrototype fp -> ppGlobalName whoToCall, fp.returns
            | Declarable.SubProgramDecl s -> ppName whoToCall, s.returns
            | Declarable.ParamDecl _
            | Declarable.VarDecl _ 
            | Declarable.ExternalVarDecl _ -> failwith "Expected to call a function but found something else!"
        let prereqStmtsLst, transInputs = 
            inputs
            |> List.map (makeTmpForComplexConst inFunction ctx)
            |> List.unzip
        let inputPrereq, processedInputs = 
            transInputs
            |> List.map (function
                | Orig input -> cpInputArgInSubprogram inFunction ctx input
                | Done d -> [], d)
            |> List.unzip
        let outputPrereq, processedOutputs =
            if inFunction then
                outputs 
                |> List.map (fun l -> cpOutputArgInFunction ctx l.lhs)
                |> List.unzip
            else
                outputs
                |> List.map (fun l -> cpOutputArgInActivity ctx l.lhs)
                |> List.unzip

        // in case we call a function that returns a non-primitive value
        if retType.IsPrimitive then
            let processedExpr =
                [processedInputs; processedOutputs]
                |> List.concat
                |> dpCommaSeparatedInParens
                |> (<^>) nameDoc
            prereqStmtsLst @ inputPrereq @ outputPrereq |> List.concat, processedExpr
        else
            let lhsName = mkIndexedAuxQNameFrom "receiverVar"
            let lhsTyp = expr.typ
            let tmpDecl = cpArrayDeclDoc (ppName lhsName) lhsTyp <^> semi
            let v = 
                { 
                    VarDecl.pos = range0
                    name = lhsName
                    datatype = lhsTyp
                    mutability = Mutability.Variable
                    initValue = {rhs = IntConst 0I; typ = Types.ValueTypes (UintType Uint8); range = expr.range} // that is garbage
                    annotation = Attribute.VarDecl.Empty
                    allReferences = HashSet() 
                }
            try ctx.tcc.nameToDecl.Add(lhsName, Declarable.VarDecl v)
            with _ -> failwith <| sprintf "Temporary variable %s already exists." (lhsName.ToString())
            let tmpLhs = LhsCur (Loc lhsName)
            let prereqReceiver, processedReceiver =
                if inFunction then cpOutputArgInFunction ctx tmpLhs
                else cpOutputArgInActivity ctx tmpLhs
            let funCall =
                [processedInputs; processedOutputs; [snd (cpOutputArgInFunction ctx tmpLhs)]] // hacky
                |> List.concat
                |> dpCommaSeparatedInParens
                |> (<^>) nameDoc
                |> (<^>) <| semi
            prereqStmtsLst @ inputPrereq @ outputPrereq @ [prereqReceiver] @ [[tmpDecl; funCall]] |> List.concat, processedReceiver

        
    | BoolConst b -> [], if b then txt "1" else txt "0"
    | IntConst i -> [], txt <| string i
    | FloatConst f -> [], f.ToDoc
    | ResetConst -> failwith "By now, the type checker should have substituted reset const by the type's default value."
    | StructConst assignments ->
        let prereqStmtsLst, processedAssignments =
            assignments
            |> List.map (fun (_,expr) -> cpExpr inFunction ctx expr)
            |> List.unzip
        prereqStmtsLst |> List.concat, processedAssignments |> dpCommaSeparatedInBraces
    | ArrayConst elems ->
        let prereqStmtsLst, processedAssignments =
            elems
            |> List.map (fun (_,expr) -> cpExpr inFunction ctx expr)
            |> List.unzip
        prereqStmtsLst |> List.concat, processedAssignments |> dpCommaSeparatedInBraces
    | Neg subExpr -> 
        let prereqStmts, processedExpr = cpExpr inFunction ctx subExpr
        prereqStmts, cpNeg processedExpr
    | Conj(s1, s2) -> binConj inFunction ctx s1 s2 
    | Disj(s1, s2) -> binDisj inFunction ctx s1 s2
    | Xor (s1, s2) -> binExpr inFunction ctx s1 s2 "^"
    | Les (s1, s2) -> binExpr inFunction ctx s1 s2 "<"
    | Leq (s1, s2) -> binExpr inFunction ctx s1 s2 "<="
    | Equ (s1, s2) ->
        match s1.typ with //do not care about s2, since type checker ensures it is the same
        | ValueTypes BoolType
        | ValueTypes (IntType _)
        | ValueTypes (UintType _)
        | ValueTypes (FloatType _) ->
            binExpr inFunction ctx s1 s2 "=="
        | ValueTypes (ValueTypes.StructType _)
        | ValueTypes (ValueTypes.ArrayType _) ->
            let prereqStmts1, processedExpr1 = cpInputArgInSubprogram inFunction ctx s1
            let prereqStmts2, processedExpr2 = cpInputArgInSubprogram inFunction ctx s2
            let length = sizeofMacro s1.typ
            let memcmp = txt "0 == memcmp" <^> dpCommaSeparatedInParens [processedExpr1; processedExpr2; length]
            prereqStmts1 @ prereqStmts2, memcmp
        | ValueTypes Void
        | AnyComposite 
        | AnyInt _ -> failwith "Error in type checker. Trying to compare void or not fully typed expressions."
        | ReferenceTypes _ -> failwith "Comparing reference types not implemented."
    | Add (s1, s2) -> binExpr inFunction ctx s1 s2 "+"
    | Sub (s1, s2) -> binExpr inFunction ctx s1 s2 "-"
    | Mul (s1, s2) -> binExpr inFunction ctx s1 s2 "*"
    | Div (s1, s2) -> binExpr inFunction ctx s1 s2 "/"
    | Mod (s1, s2) -> binExpr inFunction ctx s1 s2 "%"


let private ppParameterTml ctx tml =
    cpRenderData SubProgKind.Activity Usage.Rhs TemporalQualification.Current ctx tml ppNameInActivity
    |> snd  // take snd element of pair


let rec private genericPpTml isLocal ctx ppNameInActivity = function
    | Loc qname -> if isLocal then ppNameInActivity qname
                   else ppParameterTml ctx (Loc qname) // TODO: render input or output according to entrypoint inputs and outputs, fjg, 15.02.19
    | TypedMemLoc.FieldAccess (subtml, ident) ->
        (genericPpTml isLocal ctx ppNameInActivity subtml) <^> dot <^> txt ident
    | TypedMemLoc.ArrayAccess (subtml, idx) ->
        let preStmts, idxDoc = cpExpr false ctx idx
        preStmts @ [(genericPpTml isLocal ctx ppNameInActivity subtml) <^> (brackets idxDoc)]
        |> dpBlock
    
let ppTml isLocal ctx = genericPpTml isLocal ctx ppNameInActivity

//unused variants:
//let ppDerefTml = genericPpTml (ppName >> cpDeref >> parens)
//let ppNextTml = genericPpTml ppNextName // really?
//let ppNextDerefTml = genericPpTml (ppNextName >> cpDeref >> parens)
//let ppPrevTml = genericPpTml ppPrevName // really?

let cpExprInFunction = cpExpr true
let cpExprInActivity = cpExpr false

let rec private cpAssign inFunction ctx lhs (rhs: TypedRhs) =
    let prereqLhs, processedLhs = 
        if lhs = Wildcard then
            [], empty
        else
            let stmts, d =
                ( if inFunction then cpLhsInFunction ctx lhs
                  else cpLhsInActivity ctx lhs )
            stmts, d <+> txt "=" 
    let prereqStmts, processedRhs = cpExpr inFunction ctx rhs
    let processedAssign = 
        // TODO: here we need to discern whether we have an array and therefore
        // memcpy(..) or really a reguar =
        processedLhs <+> processedRhs <^> semi
    prereqLhs @ prereqStmts @ [processedAssign]
    |> dpBlock


let cpAssignInFunction = cpAssign true
let cpAssignInActivity = cpAssign false


let cpAssignDefaultPrevInActivity ctx qname =
    let tml = Loc qname
    let dty = getDatatypeFromTML ctx.tcc tml
    let name = ppPrevName qname
    let prereq, value = cpExpr false ctx {rhs = RhsCur tml; typ = dty; range = range0} //range0, since this does not exist in the Blech source code
    prereq
    @ [name <+> txt "=" <+> value <^> semi]
    |> dpBlock

let cpAssignPrevInActivity ctx container =
    let name = ppPrevName container
    let typ = getDatatypeFromTML ctx.tcc (Loc container)
    let prereqStmts, processedContainer = cpRhsInActivity ctx (RhsCur (Loc container))
    let init =
        match typ with
        | ValueTypes (ArrayType _) ->
            let declare = cpArrayDeclDoc name typ <^> semi
            let memcpy =
                txt "memcpy"
                <+> dpCommaSeparatedInParens
                    [ name
                      processedContainer
                      sizeofMacro typ ]
                <^> semi
            declare <..> memcpy
        | _ ->
            cpType typ 
            <+> name <+> txt "=" 
            <+> processedContainer <^> semi
    prereqStmts @ [init] |> dpBlock