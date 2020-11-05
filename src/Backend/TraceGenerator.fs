﻿// Copyright (c) 2020 - for information on the respective copyright owner
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

open Blech.Frontend.CommonTypes
open Blech.Frontend.BlechTypes
open Blech.Frontend.PrettyPrint.DocPrint

open Blech.Backend
open Blech.Backend.CPdataAccess2
open Blech.Backend.CPrinter


let private printerInterface name =
    [ txt "char * prefix"
      cpActContext name ]
    |> dpCommaSeparatedInParens

let private printerTemplate name suffix body =
    txt "void"
    <+> cpStaticName name <^> txt suffix
    <+> printerInterface name
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

let printLocal lut isLast (local: ParamDecl) =
    txt """printf("\n\t\t\t\t\"%s%s""" 
    <^> txt local.name.basicId <^> txt ("_line" + string(local.pos.StartLine))
    <^> txt """\": """
    <^> txt (getFormatStrForArithmetic local.datatype)
    <^> if isLast then txt "%s" else txt ","
    <^> txt "\", prefix" // here we use the prefix parameter of _printX
    <^> txt """, strcmp(prefix, "")? "." : "", """
    <^> renderCName Current lut local.name
    <^> if isLast then
            txt """, strcmp(prefix, "")? "," : "" """ // prefix empty means we are at top level and this is the last line - do not add a comma
        else
            empty
    <^> txt ");"

let private genStatePrinter lut compilation =
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
            printerTemplate name "_printPcs" pcPrinterBody

        // generate print function for variables
        let varsPrinterBody = 
            let callPrintersRecursively =
                actctx.subcontexts
                |> Seq.map (fun kvp -> callSubPrinter (fst kvp.Key) (snd kvp.Key) "_printLocals")
                |> dpBlock

            let printThisInstanceLocals =
                actctx.locals
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
            printerTemplate name "_printLocals" varsPrinterBody
        
        [printPcs; empty; printVars]
        |> vsep


let genStatePrinters lut compilations =
    compilations 
    |> List.map (genStatePrinter lut)
    |> dpToplevel