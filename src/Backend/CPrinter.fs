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

open Blech.Common
open Blech.Common.PPrint
open Blech.Common.Range

open Blech.Frontend.BlechTypes
open Blech.Frontend.CommonTypes
open Blech.Frontend.DocPrint
open Blech.Frontend

open CPdataAccess2


// return true if <varname> is a local variable inside activity <actname>
// and is bound to an external input or output
let isExternalGlobal (lut: TypeCheckContext) actname varname =
    match lut.nameToDecl.TryGetValue actname with
    | true, declarable ->
        match declarable with
        | ParamDecl _
        | Declarable.VarDecl _
        | Declarable.ExternalVarDecl _
        | ProcedurePrototype _ -> false // actname is a prototype and cannot contain external variable <varname>
        | ProcedureImpl impl ->
            impl.globalInputs @ impl.globalOutputsInScope
            |> List.exists (fun x -> x.name.basicId = varname.basicId)
    | false, _ -> failwithf "%A is unknown to the lookup table" actname


//=============================================================================
// Overview comments from the code generator
//=============================================================================

let cpGeneratedComment info =
    txt "/*"
    <.> txt "**" <+> info
    <.> txt "*/"

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


let cpOptModuleDoc (doc: Attribute.OtherDecl option) =
    match doc with
    | None ->
        empty  
    | Some decl ->
        match decl.doc with
        | [] -> 
            empty
        | docs->
            dpToplevelClose <| Seq.map cpDocComment docs
        
        
//=============================================================================
// Atomic language elements
//=============================================================================
let internal cpUserType typ =
    match typ with
    | ValueTypes (ValueTypes.StructType (typeName, fields)) -> 
        let cpField (field: VarDecl) =
            match field.datatype with
            | ValueTypes (ArrayType _ ) ->
                let nameDoc = txt field.name.basicId
                cpArrayDeclDoc nameDoc field.datatype <^> semi
            | _ ->
                cpType field.datatype <+> txt field.name.basicId <^> semi
        txt "typedef struct {"
        <.> (List.map cpField fields |> dpBlock |> cpIndent)
        <.> txt "}"
        <+> cpType typ
        <^> semi
    | _ -> failwith "The only printable user defined type is a value struct."

//=============================================================================
// Location accesses, input/output arguments in calls and
// intput/output formal parameters in subprogram definitions.
//=============================================================================

let internal cpDeref o = txt "*" <^> o
let internal cpRefto o = txt "&" <^> o

/// Inputs cannot be changed and may be passed in by value
// used by trace printer
let cpInputParam tcc (input: ParamDecl) =
    let iname = (cpName (Some Current) tcc input.name).Render
    // determine whether it is a primitive value type or not
    txt "const"
    <+> match input.datatype with
        | ValueTypes (ArrayType _) ->
            cpArrayDeclDoc iname input.datatype
        | _ when input.datatype.IsPrimitive ->
            cpType input.datatype <+> iname
        | _ ->
            cpType input.datatype <+> cpDeref (txt "const" <+> iname)
        
/// Outputs, PCs, Locals are changed and are always passed "by reference"
// used by trace printer
let cpOutputParam tcc (output: ParamDecl) =
    let oname = (cpName (Some Current) tcc output.name).Render
    match output.datatype with
    | ValueTypes (ArrayType _) -> cpArrayDeclDoc oname output.datatype
    | _ -> cpType output.datatype <+> cpDeref oname

// used also in TraceGenerator
let cpActContext name =
    let typename = txt "struct" <+> cpStaticName name
    let ctxname = txt CTX
    typename <+> cpDeref ctxname

let private cpRetvar = cpOutputParam

/// Translates a Blech Activity interface to a
/// C Function interface and returns a Doc representation thereof
let internal cpIface tcc (iface: Compilation) =
    [
        iface.actctx |> Option.toList |> List.map (fun _ -> cpActContext iface.name)
        iface.inputs |> List.map (cpInputParam tcc)
        iface.outputs |> List.map (cpOutputParam tcc)
        iface.retvar |> Option.toList |> List.map (cpRetvar tcc)
    ]
    |> List.concat
    |> dpCommaSeparatedInParens

/// Print an activity interface that consists of the context only
/// This is needed for rendering the _init functions
let internal cpActCtxIfaceOnly (iface: Compilation) =
    iface.actctx 
    |> Option.toList 
    |> List.map (fun _ -> cpActContext iface.name)
    |> dpCommaSeparatedInParens

/// Translates a Blech Function interface to a
/// C Function interface and returns a Doc representation thereof
let internal cpFunctionIface tcc (iface: Compilation) =
    let cargs = 
        List.concat [
            iface.inputs |> List.map (cpInputParam tcc)
            iface.outputs |> List.map (cpOutputParam tcc)
            iface.retvar |> Option.toList |> List.map (cpRetvar tcc)
        ]
    (if List.isEmpty cargs then [txt "void"] else cargs)
    |> dpCommaSeparatedInParens

/// Translate the locals, retvar, and program counters, of the entry point as a list of declarations of static global variables.
// Note no initialisation takes places here, this is done in the entry point
// activity in the surface.
let internal cpMainStateAsStatics (iface: Compilation) =
    let typename = txt "static struct" <+> cpStaticName iface.name
    let ctxname = txt CTX
    typename <+> ctxname <^> semi

/// Translate the inputs and outputs of the entry point as a list of declarations of static global variables 
let internal cpMainParametersAsStatics tcc (iface: Compilation) =
    let render n = (cpName (Some Current) tcc n).Render
    [
        iface.inputs
        iface.outputs
    ]
    |> List.concat
    |> List.map (fun p -> txt "static" <+> cpArrayDeclDoc (render p.name) p.datatype <^> semi)
    |> dpBlock

let internal cpContextTypeDeclaration lut (comp: Compilation) =
    match comp.actctx with 
    | None -> empty // this is a function, nothing to print
    | Some _ -> // ok, print activity context struct
        let typename = cpStaticName comp.name
        let locals = 
            let renderNameForCtx name =
                if isExternalGlobal lut comp.name name then
                    // if an external is the activity context, it is there because we use the previous value
                    assembleName BLC (name.prefix @ [PREV]) name.basicId
                else
                    assembleName BLC name.prefix name.basicId
            // in order to avoid clashes between a Blech variable "pc_1" and 
            // a context element pc_1, we need the blc_ prefix
            comp.GetActCtx.locals
            |> List.map (fun local -> cpArrayDeclDoc (renderNameForCtx local.name) local.datatype <^> semi)
            |> dpBlock
        let pcs = 
            comp.GetActCtx.pcs.AsList
            |> List.map (fun pc -> txt "blc_pc_t" <+> txt pc.name.basicId <^> semi)
            |> dpBlock
        let subctx =
            comp.GetActCtx.subcontexts
            |> Seq.map (fun subctx -> txt "struct" 
                                    <+> cpStaticName (snd subctx) // C type name
                                    <+> txt (fst subctx) <^> txt "_" <^> cpStaticName (snd subctx) // field name
                                    <^> semi)
            |> dpBlock
        let fields = // we do this little detour to remove empty lines
            [ locals
              pcs
              subctx ]
            |> dpBlock

        txt "struct" <+> typename <+> txt "{"
        <.> cpIndent fields
        <.> txt "}" <^> semi

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

let internal cpExternFunction tcc docs name iface (returns: ValueTypes) =
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
            TypeCheckContext.addDeclToLut tcc qname (Declarable.ParamDecl v)
            {iface with retvar = Some v}, cpType (ValueTypes Void)

    let prototype = 
        retType
        <+> cpStaticName name
        <+> cpFunctionIface tcc completeInterface
        <^> semi

    cpOptDocComments docs 
    |> dpOptLinePrefix
    <| prototype


let internal cpDirectCCall tcc (fp: ProcedurePrototype) =
    let args =
        fp.inputs @ fp.outputs
        |> List.map (fun p -> (renderCName Current tcc p.name))
    let argsWithReturn =
        if fp.returns.IsPrimitive then args
        else args @ [txt "retvar"]
    let cbinding = fp.annotation.TryGetCBinding
    let call = 
        let sargs = List.map (render None) argsWithReturn
        Bindings.replaceParameters (Option.get cbinding) sargs
        |> Bindings.toDoc
    let macro = 
        (txt "#define"
        <+> cpStaticName fp.name
        <^> dpCommaSeparatedInParens argsWithReturn
        <.> (cpIndent call))
        |> groupWith (txt " \\")

    cpOptDocComments fp.annotation.doc
    |> dpOptLinePrefix
    <| macro