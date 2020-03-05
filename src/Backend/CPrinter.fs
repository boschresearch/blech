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

module Blech.Backend.CPrinter

open System.Collections.Generic

open Blech.Common.PPrint
open Blech.Common.Range

open Blech.Frontend.BlechTypes
open Blech.Frontend.CommonTypes
open Blech.Frontend.PrettyPrint.DocPrint
open Blech.Frontend

open CPdataAccess


//=============================================================================
// Overview comments from the code generator
//=============================================================================

let cpGeneratedComment info =
    txt "/*"
    <.> txt "**" <+> info
    <.> txt "*/"

//=============================================================================
// Program names tick, init, printstate 
//=============================================================================
let cpProgramName programQName = 
    translateQnameToProgramName programQName
    |> txt


//=============================================================================
// Doc Comments
//=============================================================================

// Some allowed Blech doc comments generate illegal C comments, like
// /**/mydoc*/ -- not allowed in C but in Blech
// /// mydoc */  -- creates /**  mydoc */ */, which closes too early
let cpDocComment (dc: Attribute.Attribute) = 
    match dc with
    | Attribute.LineDoc doc ->
        txt "/**" <+> txt doc <+> txt "*/" // end of line comments are not allowed in C89
    | Attribute.BlockDoc doc ->
        txt "/**" <^> txt doc <^> txt "*/" // <+> prevents pathologic doc comments like /**/mydoc */
    | _ ->
        empty
        

let cpOptDocComments (docs: Attribute.Attribute list) =
    match docs with
    | [] ->
        None
    | _ ->
        Some (dpToplevelClose <| Seq.map cpDocComment docs)
        
//=============================================================================
// Atomic language elements
//=============================================================================
let internal cpUserType typ =
    match typ with
    | ValueTypes (ValueTypes.StructType (_, typeName, fields)) -> 
        let cpField (field: VarDecl) =
            match field.datatype with
            | ValueTypes (ArrayType _ ) ->
                let nameDoc = txt field.name.basicId
                cpArrayDeclDoc nameDoc field.datatype <^> semi
            | _ ->
                cpType field.datatype <+> txt field.name.basicId <^> semi
        let ctype = 
            txt "struct" <+> ppGlobalName typeName <+> txt "{"
            <.> (List.map cpField fields |> dpBlock |> cpIndent)
            <.> txt "};"
        ctype
    | _ -> failwith "The only printable user defined type is a value struct."

//=============================================================================
// Location accesses, input/output arguments in calls and
// intput/output formal parameters in subprogram definitions.
//=============================================================================

/// Inputs cannot be changed and may be passed in by value
let private cpInputParam (input: ParamDecl) =
    // determine whether it is a primitive value type or not
    txt "const"
    <+> match input.datatype with
        | ValueTypes (ArrayType _) ->
            cpArrayDecl input.name input.datatype
        | _ when input.datatype.IsPrimitive ->
            cpType input.datatype <+> ppName (input.name)
        | _ ->
            cpType input.datatype <+> cpDeref (txt "const" <+> ppName (input.name))
        
/// Outputs, PCs, Locals are changed and are always passed "by reference"
let private cpOutputParam (output: ParamDecl) =
    match output.datatype with
    | ValueTypes (ArrayType _) -> cpArrayDecl output.name output.datatype
    | _ -> cpType output.datatype <+> cpDeref (ppName (output.name))


let private cpPc (pc: ParamDecl) = 
    txt "blc_pc_t" <+> cpDeref (ppName (pc.name))


// let private cpLocal = cpOutputParam
/// Local variable parameter for activity
let private cpLocal (local: ParamDecl) =
    match local.datatype with
    | ValueTypes (ArrayType _) -> cpArrayDeclInActivity local.name local.datatype
    | _ -> cpType local.datatype <+> cpDeref (ppNameInActivity (local.name))

let private cpRetvar = cpOutputParam

/// Translates a Blech Activity interface to a
/// C Function interface and returns a Doc representation thereof
let internal cpIface (iface: Iface) =
    [
        iface.inputs |> List.map cpInputParam
        iface.outputs |> List.map cpOutputParam
        iface.locals |> List.map cpLocal
        iface.pcs |> List.map cpPc
        iface.retvar |> Option.toList |> List.map cpRetvar
    ]
    |> List.concat
    |> dpCommaSeparatedInParens

/// Translates a Blech Function interface to a
/// C Function interface and returns a Doc representation thereof
let internal cpFunctionIface (iface: Iface) =
    let cargs = 
        List.concat [
            iface.inputs |> List.map cpInputParam
            iface.outputs |> List.map cpOutputParam
            iface.retvar |> Option.toList |> List.map cpRetvar
        ]
    (if List.isEmpty cargs then [txt "void"] else cargs)
    |> dpCommaSeparatedInParens

/// Translate the locals, retvar, and program counters, of the entry point as a list of declarations of static global variables.
// Note no initialisation takes places here, this is done in the entry point
// activity in the surface.
let internal cpMainStateAsStatics (iface: Iface) =
    [
        iface.locals
        iface.retvar |> Option.toList
    ]
    |> List.concat
    |> List.map (fun p -> txt "static" <+> cpArrayDeclInActivity p.name p.datatype <^> semi)
    |> List.append <| List.map (fun (p: ParamDecl) -> txt "static" <+> txt "blc_pc_t" <+> ppName (p.name) <^> semi) iface.pcs
    |> dpBlock

/// Translate the inputs and outputs of the entry point as a list of declarations of static global variables 
let internal cpMainParametersAsStatics (iface: Iface) =
    [
        iface.inputs
        iface.outputs
    ]
    |> List.concat
    |> List.map (fun p -> txt "static" <+> cpArrayDeclInActivity p.name p.datatype <^> semi)
    |> dpBlock


//=============================================================================
// Statements
//=============================================================================

let internal cpIfOnly cond body =
    txt "if (" <+> cond <+> txt ") {"
    <.> cpIndent body
    <.> txt "}"

let internal cpIfElse cond ifBranch elseBranch =
    txt "if (" <+> cond <+> txt ") {"
    <.> cpIndent ifBranch
    <.> txt "} else {"
    <.> cpIndent elseBranch
    <.> txt "}"

/// produces an if (...){...} [else if (...){...}]* 
let internal cpIfElseIf condsAndBlocks =
    match condsAndBlocks with
    | [] -> txt ""
    | [cond, block] -> cpIfOnly cond block
    | (cond, block) :: rest ->
        let firstIf =
            txt "if (" <+> cond <+> txt ") {"
            <.> cpIndent block
            <.> txt "}"
        let elseIf =
            rest
            |> List.map (fun (c, b) ->
                txt "else if (" <+> c <+> txt ") {"
                <.> cpIndent b
                <.> txt "}"
                )
            |> hsep
        hsep
        <| [ firstIf
             elseIf ]
        

let internal cpWhile cond body =
    txt "while (" <+> cond <+> txt ") {"
    <.> cpIndent body
    <.> txt "}"

let internal cpRepeatUntil cond body =
    txt "do {"
    <.> cpIndent body
    <.> txt "} while (" <+> cond <+> txt ")" <^> semi


//=============================================================================
// Function prototypes
//=============================================================================

let internal cpExternFunction docs name iface (returns: ValueTypes) =
    // decide whether a return variable is needed based on returns type
    let completeInterface, retType =
        if returns.IsPrimitive then
            iface, cpType (ValueTypes returns)
        else
            let qname = QName.Create name.moduleName (name.prefix @ [name.basicId]) "retvar" Dynamic
            let v = { name = qname
                      pos = range.Zero
                      datatype = ValueTypes returns
                      isMutable = true 
                      allReferences = HashSet() }
            // we never refer to this variable in code generation, so there is no need to add it any context
            {iface with retvar = Some v}, cpType (ValueTypes Void)

    let prototype = 
        retType
        <+> ppGlobalName name
        <+> cpFunctionIface completeInterface
        <^> semi

    cpOptDocComments docs 
    |> dpOptLinePrefix
    <| prototype


let internal cpDirectCCall (fp: FunctionPrototype) =
    let args =
        List.map (fun (p: ParamDecl) -> ppName p.name) (fp.inputs @ fp.outputs) 
    let cbinding = fp.annotation.TryGetCBinding
    let call =
        txt (Option.get cbinding)
        <^> dpCommaSeparatedInParens args
    let macro = 
        (txt "#define"
        <+> ppName fp.name
        <^> dpCommaSeparatedInParens args
        <.> (cpIndent <| parens call))
        |> groupWith (txt " \\")

    cpOptDocComments fp.annotation.doc
    |> dpOptLinePrefix
    <| macro