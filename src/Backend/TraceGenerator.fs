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

module Blech.Backend.TraceGenerator

open Blech.Common.PPrint
open Blech.Common.Range

open Blech.Frontend.CommonTypes
open Blech.Frontend.Constants
open Blech.Frontend.BlechTypes
open Blech.Frontend.PrettyPrint.DocPrint
open Blech.Frontend.TypeCheckContext

open Blech.Backend
open Blech.Backend.CPdataAccess2
open Blech.Backend.CPrinter


let private printerInterface tcc name ins outs =
    [ [txt "char * prefix"]
      [cpActContext name]
      ins |> List.map (cpInputParam tcc)
      outs |> List.map (cpOutputParam tcc) ]
    |> List.concat
    |> dpCommaSeparatedInParens

let private printerTemplate lut name suffix body ins outs =
    txt "void"
    <+> cpStaticName name <^> txt suffix
    <+> printerInterface lut name ins outs
    <+> txt "{"
    <.> cpIndent body
    <.> txt "}"

let callSubPrinter callerPc name suffix =
    let mangledName = txt callerPc <^> txt "_" <^> cpStaticName name
    let prefixvar = 
        txt "sprintf(buffer,\"%s%s"
        <^> mangledName
        <^> txt "\", prefix"
        <^> txt """, strcmp(prefix, "")? "." : "");"""
        
    let args = 
        [ txt "buffer" // glue together path through state struct
          txt "&blc_blech_ctx->" <^> mangledName] // sub-context
        |> dpCommaSeparatedInParens
    [ prefixvar
      cpStaticName name <^> txt suffix <^> args <^> semi ]
    |> dpBlock

let printPc isLast (pc: ParamDecl) =
    // generated line should like like
    // printf("\"%s.pc: %u\"", prefix, ctx->pc);
    txt """printf("\n\t\t\t\t\"%s%s""" 
    <^> txt pc.name.basicId 
    <^> txt """\": %u"""
    <^> if isLast then txt "%s" else txt ","
    <^> txt "\", prefix" // here we use the prefix parameter of _printX
    <^> txt """, strcmp(prefix, "")? "." : "", """
    <^> cpPcName pc.name
    <^> if isLast then
            txt """, strcmp(prefix, "")? "," : "" """ // prefix empty means we are at top level and this is the last line - do not add a comma
        else
            empty
    <^> txt ");"

let getFormatStrForArithmetic (dty: Types) =
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

let rec printTml level lut isLast tml (pos: range) = 
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
    | ValueTypes _ when dty.IsPrimitive ->
        // do the printing
        txt <| sprintf "printf(\"\\n\\t\\t\\t\\t%s" tabs
        <^> txt ident
        <^> txt (getFormatStrForArithmetic dty)
        <^> if isLast && level = 0 then txt "%s" 
            elif isLast && level > 0 then empty // do not put a , behind the last element of struct or array
            else txt "," // not last, always comma
        <^> txt "\","
        <^> (cpTml Current lut tml).Render
        <^> if level = 0 && isLast then
                txt """, strcmp(prefix, "")? "," : "" """ // prefix empty means we are at top level and this is the last line - do not add a comma
            else empty 
        <^> txt ");"
    | ValueTypes (ValueTypes.StructType (_, _, fields)) ->
        // access each field and call recursively
        let structContents =
            fields
            |> List.rev
            |> function
                | [] -> []
                | f :: fs ->
                    printTml (level + 1) lut true (tml.AddFieldAccess f.name.basicId) pos
                    :: List.map (fun (x: VarDecl) -> printTml (level + 1) lut false (tml.AddFieldAccess x.name.basicId) pos) fs
            |> List.rev
        let openStruct =
            txt <| sprintf "printf(\"\\n\\t\\t\\t\\t%s" tabs
            <^> txt ident
            <^> txt """{");"""
        let closeStruct =
            txt <| sprintf "printf(\"\\n\\t\\t\\t\\t%s}" tabs
            //<^> if isLast then empty else txt ","
            <^> if level = 0 && isLast then
                    txt """%s", strcmp(prefix, "")? "," : "" """ // prefix empty means we are at top level and this is the last line - do not add a comma
                elif isLast then txt "\""
                else txt ",\""
            <^> txt ");"
        openStruct :: structContents @ [closeStruct]
        |> dpBlock
    | ValueTypes (ArrayType (size,_)) ->
        let mkIdxOf j =
            { rhs = IntConst (Int.I32 j)
              typ = ValueTypes (IntType Int32)
              range = range0 }
        let openArray =
            txt <| sprintf "printf(\"\\n\\t\\t\\t\\t%s" tabs
            <^> txt ident
            <^> txt """[");"""
        let closeArray =
            txt <| sprintf "printf(\"\\n\\t\\t\\t\\t%s]" tabs
            //<^> if isLast then empty else txt ","
            <^> if level = 0 && isLast then
                    txt """%s", strcmp(prefix, "")? "," : "" """ // prefix empty means we are at top level and this is the last line - do not add a comma
                elif isLast then txt "\""
                else txt ",\""
            <^> txt ");"
        let intsize = (int)size // an array with max_int many entries is at least 2GB large, so before we run into casting problems here the trace printing would already be intractable
        let arrayContents =
            [for i in 0 .. intsize - 2 -> printTml (level + 1) lut false (tml.AddArrayAccess (mkIdxOf i)) pos]
            @ [for i in intsize - 1 .. intsize - 1 -> printTml (level + 1) lut true (tml.AddArrayAccess (mkIdxOf i)) pos]
        openArray :: arrayContents @ [closeArray]
        |> dpBlock
    | _ -> failwith "Only value types implemented."

let printLocal lut isLast (local: ParamDecl) =
    //txt """printf("\n\t\t\t\t\"%s%s""" 
    //<^> txt local.name.basicId <^> txt ("_line" + string(local.pos.StartLine))
    //<^> txt """\": """
    //<^> txt (getFormatStrForArithmetic local.datatype)
    //<^> if isLast then txt "%s" else txt ","
    //<^> txt "\", prefix" // here we use the prefix parameter of _printX
    //<^> txt """, strcmp(prefix, "")? "." : "", """
    //<^> renderCName Current lut local.name
    //<^> if isLast then
    //        txt """, strcmp(prefix, "")? "," : "" """ // prefix empty means we are at top level and this is the last line - do not add a comma
    //    else
    //        empty
    //<^> txt ");"
    printTml 0 lut isLast (TypedMemLoc.Loc local.name) local.pos

let private genStatePrinter lut compilation amIentryPoint =
    match compilation.actctx with
    | None -> empty
    | Some actctx ->
        let name = compilation.name
        
        // generate print function for pcs
        let pcPrinterBody =
            let callPrintersRecursively =
                actctx.subcontexts
                |> Seq.map (fun kvp -> callSubPrinter (fst kvp.Key) (snd kvp.Key) "_printPcs")
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

            [ txt "char buffer[10000];"
              callPrintersRecursively
              printThisInstancePcs ]
            |> dpBlock

        let printPcs =
            printerTemplate lut name "_printPcs" pcPrinterBody [] []

        // generate print function for variables
        let varsPrinterBody = 
            let callPrintersRecursively =
                actctx.subcontexts
                |> Seq.map (fun kvp -> callSubPrinter (fst kvp.Key) (snd kvp.Key) "_printLocals")
                |> dpBlock

            let printThisInstanceLocals =
                let allLocals =
                    if amIentryPoint then compilation.inputs else []
                    @ if amIentryPoint then compilation.outputs else []
                    @ actctx.locals
                allLocals
                |> function
                | [] -> []
                | l :: ls ->
                    printLocal lut true l :: List.map (printLocal lut false) ls
                |> List.rev
                |> dpBlock

            [ txt "char buffer[10000];"
              callPrintersRecursively
              printThisInstanceLocals ]
            |> dpBlock
        
        let printVars =
            let ins = if amIentryPoint then compilation.inputs else []
            let outs = if amIentryPoint then compilation.outputs else []
            printerTemplate lut name "_printLocals" varsPrinterBody ins outs
        
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