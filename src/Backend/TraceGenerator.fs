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
/// This module generates C code for printing execution traces in JSON format.
//=============================================================================

module Blech.Backend.TraceGenerator

open Blech.Common.PPrint
open Blech.Common.Range

open Blech.Frontend
open Blech.Frontend.CommonTypes
open Blech.Frontend.Constants
open Blech.Frontend.BlechTypes
open Blech.Frontend.DocPrint
open Blech.Frontend.TypeCheckContext

open Blech.Backend
open Blech.Backend.CPdataAccess2
open Blech.Backend.CPrinter


/// Constants
let printPcSuffix = "_printPcs"
let printLocalsSuffix = "_printLocals"
let emptyCString = "\"\"" // also used in ProgramGenerator.fs
let private BUFFER = "buffer"
let private BUFFER_SIZE = 10000
let private BUFFER_DECL = sprintf "char %s[%d];" BUFFER BUFFER_SIZE
let private PREFIX = "prefix"
let private PREFIX_DECL = "char * " + PREFIX
let private QT = "\"" // a double quote character "
let private cCodeDotIfPrefixExists = sprintf "strcmp(%s, %s)? \".\" : %s" PREFIX emptyCString emptyCString
let private cCodeCommaIfNotTopLevel = sprintf "strcmp(%s, %s)? \",\" : %s" PREFIX emptyCString emptyCString //strcmp(prefix, "")? "," : ""
let private cCodeAddComma = "retcode?printf(\",\"):0;" // 0 is used as an empty expression or no-op

let private cCodeAppendArg accumulator arg =
    accumulator + ", " + arg

let private cCodePrintf format args =
    args
    |> List.fold cCodeAppendArg ""
    |> sprintf "printf(%s%s);" (QT + format + QT)

let private cCodeSprintf destination format args =
    args
    |> List.fold cCodeAppendArg ""
    |> sprintf "sprintf(%s, %s%s);" destination (QT + format + QT)


let private printerInterface lut name ins outs = 
    [ [txt PREFIX_DECL]
      [cpActContext name]
      ins |> List.map (cpInputParam lut)
      outs |> List.map (cpOutputParam lut) ]
      |> List.concat
      |> dpCommaSeparatedInParens

/// int <name>_<suffix> (char * prefix, struct <name> blc_blech_ctx, <ins>, <outs>) { <body> }
/// a printer for local variables returns 1 if it printed something 
/// (there may be activities without local variables, 
/// then there is nothing to print and 0 is returned)
let private printerTemplate lut name suffix body ins outs =
    txt "int"
    <+> cpStaticName name <^> txt suffix
    <+> printerInterface lut name ins outs
    <+> txt "{"
    <.> cpIndent body
    <.> txt "}"

/// int <name>_<suffix> (char * prefix, struct <name> blc_blech_ctx, <ins>, <outs>);
let private printerPrototypeTemplate lut name suffix ins outs =  
    txt "int"
    <+> cpStaticName name <^> txt suffix
    <+> printerInterface lut name ins outs
    <^> semi
    

let private callSubPrinter callerPc name suffix =
    let mangledName = callerPc + "_" + (cpStaticName name |> render None) // doppelt gemoppelt
    let subcontext = renderSubContext callerPc name                       // <-^
    let prefixvar = 
        let format = "%s%s" + mangledName 
        cCodeSprintf BUFFER format [PREFIX; cCodeDotIfPrefixExists]
        |> txt
    let args = 
        [ txt BUFFER // glue together path through state struct
          subcontext] // sub-context
        |> dpCommaSeparatedInParens
    [ prefixvar
      txt "retcode =" <+> cpStaticName name <^> txt suffix <^> args <^> semi ]
    |> dpBlock

let private printPc isLast (pc: ParamDecl) =
    // generated line should like like
    // printf("\"%s.pc: %u\"", prefix, ctx->pc);
    let format = "\\n\\t\\t\\t\\t\\\"%s%s" + pc.name.basicId + "\\\": %u" + if isLast then "%s" else ","
    let args = [ PREFIX
                 cCodeDotIfPrefixExists
                 cpPcName pc.name |> render None
                 if isLast then 
                    cCodeCommaIfNotTopLevel ]
    cCodePrintf format args
    |> txt

let private getFormatStrForArithmetic (dty: Types) =
    assert dty.IsPrimitive
    match dty with
    | ValueTypes (BoolType) -> "%d"
    | ValueTypes (FloatType Float64)
    | ValueTypes (FloatType Float32) -> "%e"
    | ValueTypes (IntType Int64) -> "%lld"
    | ValueTypes (IntType Int32) -> "%ld"
    | ValueTypes (IntType Int16) -> "%hd"
    | ValueTypes (IntType Int8) -> "%hd" // should be hhd since C99
    | ValueTypes (NatType Nat64) -> "%llu"
    | ValueTypes (NatType Nat32) -> "%lu"
    | ValueTypes (NatType Nat16) -> "%hu"
    | ValueTypes (NatType Nat8) -> "%hu" // should be hhu since C99
    | ValueTypes (BitsType Bits64) -> "%llu"
    | ValueTypes (BitsType Bits32) -> "%lu"
    | ValueTypes (BitsType Bits16) -> "%hu"
    | ValueTypes (BitsType Bits8) -> "%hu" // should be hhu since C99
    | _ -> failwithf "No format string for composite data type %A." dty

let rec private printTml isExternalGlobal level lut isLast (tml: TypedMemLoc) (pos: range) = 
    let timepoint =
        if isExternalGlobal tml.QNamePrefix then Previous
        else Current
    let dty = getDatatypeFromTML lut tml
    let ident =
        let innerIdent =
            if level = 0 then tml.QNamePrefix.basicId + ("_line" + string(pos.StartLine))
            else
                match tml with 
                | TypedMemLoc.Loc name -> name.basicId
                | TypedMemLoc.FieldAccess (_,i) -> i
                | TypedMemLoc.ArrayAccess (_,i) -> "" //i.ToString()
        if System.String.IsNullOrWhiteSpace innerIdent then ""
        else "\\\"" + innerIdent + "\\\": "
    let tabs = String.replicate level "\\t"
    match dty with
    | ValueTypes (OpaqueSimple _)
    | ValueTypes (OpaqueArray _)
    | ValueTypes (OpaqueStruct _) ->
        // do the printing
        let format = 
            sprintf "\\n\\t\\t\\t\\t%s" tabs
            + ident
            + "%s"
            + if isLast then "" 
              else ","
        let args =
            "\"\\\"opaque\\\"\""
        cCodePrintf format [args]
        |> txt
    | ValueTypes _ when dty.IsPrimitive ->
        // do the printing
        let format = 
            sprintf "\\n\\t\\t\\t\\t%s" tabs
            + ident
            + getFormatStrForArithmetic dty
            + if isLast then "" 
              else ","
        let args = 
            ((cpTml timepoint lut tml).Render |> render None)
        cCodePrintf format [args]
        |> txt
    | ValueTypes (ValueTypes.StructType (_, fields)) ->
        // access each field and call recursively
        let structContents =
            fields
            |> List.rev
            |> function
                | [] -> []
                | f :: fs ->
                    printTml isExternalGlobal (level + 1) lut true (tml.AddFieldAccess f.name.basicId) pos
                    :: List.map (fun (x: VarDecl) -> printTml isExternalGlobal (level + 1) lut false (tml.AddFieldAccess x.name.basicId) pos) fs
            |> List.rev
        let openStruct =
            let format = 
                sprintf "\\n\\t\\t\\t\\t%s" tabs
                + ident
                + "{"
            cCodePrintf format []
            |> txt
        let closeStruct =
            let format = 
                sprintf "\\n\\t\\t\\t\\t%s}" tabs
                + if isLast then "" 
                  else ","
            let args = []
            cCodePrintf format args
            |> txt
        openStruct :: structContents @ [closeStruct]
        |> dpBlock
    | ValueTypes (ArrayType (size,_)) ->
        let mkIdxOf j =
            { rhs = IntConst (Int.I32 j)
              typ = ValueTypes (IntType Int32)
              range = range0 }
        let openArray =
            let format = 
                sprintf "\\n\\t\\t\\t\\t%s" tabs
                + ident
                + "["
            cCodePrintf format []
            |> txt
        let closeArray =
            let format =
                sprintf "\\n\\t\\t\\t\\t%s]" tabs
                + if isLast then "" 
                  else ","
            let args = []
            cCodePrintf format args
            |> txt
        let intsize = (int)size // an array with max_int many entries is at least 2GB large, so before we run into casting problems here the trace printing would already be intractable
        let arrayContents =
            [for i in 0 .. intsize - 2 -> printTml isExternalGlobal (level + 1) lut false (tml.AddArrayAccess (mkIdxOf i)) pos]
            @ [for i in intsize - 1 .. intsize - 1 -> printTml isExternalGlobal (level + 1) lut true (tml.AddArrayAccess (mkIdxOf i)) pos]
        openArray :: arrayContents @ [closeArray]
        |> dpBlock
    | _ -> failwith "Only value types implemented."

let private printLocal isExternalGlobal lut isLast (local: ParamDecl) =
    printTml isExternalGlobal 0 lut isLast (TypedMemLoc.Loc local.name) local.pos

let private genStatePrinter lut compilation amIentryPoint =
    match compilation.actctx with
    | None -> empty
    | Some actctx ->
        let name = compilation.name
        
        // generate print function for pcs
        let pcPrinterBody =
            let callPrintersRecursively =
                actctx.subcontexts
                |> Seq.map (fun subctx -> callSubPrinter (fst subctx) (snd subctx) printPcSuffix)
                |> dpBlock

            let printThisInstancePcs =
                actctx.pcs.AsList
                |> List.rev
                |> function
                    | [] -> []
                    | p :: ps ->
                        printPc true p :: List.map (printPc false) ps
                |> List.rev
                |> dpBlock

            [ txt BUFFER_DECL
              txt "int retcode = 0;" // irrelevant here but is needed for the call
              callPrintersRecursively
              printThisInstancePcs
              txt "return 0;" ] // again irrelevant for printing pcs
            |> dpBlock

        let printPcs =
            printerTemplate lut name printPcSuffix pcPrinterBody [] []

        // generate print function for variables
        let varsPrinterBody = 
            let callPrintersRecursively =
                actctx.subcontexts
                |> Seq.map (fun subctx -> callSubPrinter (fst subctx) (snd subctx) printLocalsSuffix)
                |> punctuate (txt cCodeAddComma <.> txt "retcode = 0;")
                |> dpBlock

            let printThisInstanceLocals =
                let allLocals =
                    if amIentryPoint then compilation.inputs else []
                    @ if amIentryPoint then compilation.outputs else []
                    @ actctx.locals
                match allLocals with
                | [] -> []
                | _ ->
                    let allLocalsPrinted =
                        allLocals
                        |> function
                        | [] -> []
                        | l :: ls ->
                            printLocal (isExternalGlobal lut name) lut true l :: List.map (printLocal (isExternalGlobal lut name) lut false) ls
                        |> List.rev
                        |> dpBlock
                    [ txt cCodeAddComma
                      allLocalsPrinted ]

            [ txt BUFFER_DECL
              txt "int retcode = 0;"
              callPrintersRecursively
              printThisInstanceLocals |> dpBlock
              if List.isEmpty printThisInstanceLocals then txt "return (0 || retcode);" else txt "return 1;" ]
            |> dpBlock
        
        let printVars =
            let ins = if amIentryPoint then compilation.inputs else []
            let outs = if amIentryPoint then compilation.outputs else []
            printerTemplate lut name printLocalsSuffix varsPrinterBody ins outs
        
        [printPcs; empty; printVars]
        |> vsep


let genStatePrinters lut compilations entryPointOpt =
    let ep =
        match entryPointOpt with
        | None -> QName.CreateAuxiliary [] "" // empty name, no real activity has an empty name
        | Some name -> name
    compilations 
    |> List.map (fun c -> genStatePrinter lut c (c.name = ep))
    |> dpToplevel


let private genStatePrinterPrototype lut compilation amIentryPoint =
    match compilation.actctx with
    | None -> empty
    | Some actctx ->
        let name = compilation.name
        
        // generate print function protoypes
        let printPcsPrototype =
            printerPrototypeTemplate lut name printPcSuffix [] []

        let printVarsPrototype =
            let ins = if amIentryPoint then compilation.inputs else []
            let outs = if amIentryPoint then compilation.outputs else []
            printerPrototypeTemplate lut name printLocalsSuffix ins outs
        
        [printPcsPrototype; empty; printVarsPrototype]
        |> vsep


let genStatePrinterPrototypes lut compilations entryPointOpt =
    let ep =
        match entryPointOpt with
        | None -> QName.CreateAuxiliary [] "" // empty name, no real activity has an empty name
        | Some name -> name
    compilations 
    |> List.map (fun c -> genStatePrinterPrototype lut c (c.name = ep))
    |> dpToplevel