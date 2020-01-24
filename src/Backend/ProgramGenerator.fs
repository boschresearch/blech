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

/// This module contains all functionality which is specific for the
/// of the Blech program C functions.

[<RequireQualifiedAccess>]
module Blech.Backend.ProgramGenerator

open Blech.Common
open Blech.Common.PPrint

open Blech.Frontend.CommonTypes
open Blech.Frontend.BlechTypes  
open Blech.Frontend.PrettyPrint.DocPrint
open Blech.Frontend.TypeCheckContext

open Blech.Backend

open CPdataAccess
open CPrinter


let private cpByPointer param = chr '*' <^> param

/// Inputs of the main functions 'tick' and 'init'
let private cpMainInputParam scalarPassByPointer (input: ParamDecl) =
    // determine whether it is a primitive value type or not
    txt "const"
    <+> match input.datatype with
        | ValueTypes (ArrayType _) ->
            cpArrayDeclDoc (ppStaticName input.name) input.datatype
        | ValueTypes typ when typ.IsPrimitive ->
            cpType input.datatype
            <+> if scalarPassByPointer then 
                    cpByPointer (ppStaticName input.name)
                else 
                    ppStaticName input.name
        | _ ->
            cpType input.datatype <+> cpDeref (txt "const" <+> ppStaticName input.name)


/// Outputs of the main functions 'tick' and 'init'. 
let private cpMainOutputParam (output: ParamDecl) =
    match output.datatype with
    | ValueTypes (ArrayType _) -> cpArrayDeclDoc (ppStaticName output.name) output.datatype
    | _ -> cpType output.datatype <+> cpDeref (ppStaticName output.name)
        

// translates the interface of the EntryPoint activity to C function interface for 'tick' and 'init'
let private cpMainIface scalarPassByPointer (iface: Iface) =
    let cargs = 
        List.concat [
            iface.inputs |> List.map (cpMainInputParam scalarPassByPointer)
            iface.outputs |> List.map cpMainOutputParam
        ]
    (if List.isEmpty cargs then [txt "void"] else cargs)
    |> dpCommaSeparatedInParens


/// The following are specific functions to call the entry point activity from the tick function
/// They are called nowhere else

let private staticStateToArgument (p: ParamDecl) =
    match p.datatype with
    | ValueTypes BoolType | ValueTypes (IntType _) | ValueTypes (NatType _) | ValueTypes (FloatType _) 
        when not p.isMutable ->
        ppNameInGlobalCall p.name
    | ValueTypes (ArrayType _) -> ppNameInGlobalCall p.name
    | _ -> cpRefto <| ppNameInGlobalCall p.name


/// Call to entry point activity
let private cpGlobalCall primitivePassByAddress (iface: Iface) =
    let inputParamToArgument (p: ParamDecl) = 
        match p.datatype with
        | ValueTypes vt when vt.IsPrimitive ->
            if primitivePassByAddress then
                cpDeref (ppNameInGlobalCall p.name)
            else
                ppNameInGlobalCall p.name
        | ValueTypes _ ->
            ppNameInGlobalCall p.name
        | _ ->
            cpRefto <| ppNameInGlobalCall p.name

    let outputParamToArgument (p: ParamDecl) = 
            ppNameInGlobalCall p.name

    [
        iface.inputs |> List.map inputParamToArgument
        iface.outputs |> List.map outputParamToArgument
        iface.locals |> List.map staticStateToArgument
        iface.pcs |> List.map staticStateToArgument
        iface.retvar |> Option.toList |> List.map staticStateToArgument
    ]
    |> List.concat
    |> dpCommaSeparatedInParens


/// Call parameters for the tick and the printState functions
/// To be used from the test app only

let internal cpAppCall (entryPointIface: Iface) =
    [
        entryPointIface.inputs |> List.map staticStateToArgument
        entryPointIface.outputs |> List.map staticStateToArgument
    ]
    |> List.concat
    |> dpCommaSeparatedInParens


/// Generate a C function "void tick(...)" which calls
/// enters the entry point activity in every tick.
let internal mainCallback primitivePassByAddress tick entryName entryIface = 
    // Generates a c function call to the  EntryPoint activity
    let entryPointCall =
        ppName entryName
        <^> cpGlobalCall primitivePassByAddress entryIface 
        <^> semi
        |> cpIndent

    txt "void"
    <+> cpProgramName tick
    <+> cpMainIface primitivePassByAddress entryIface 
    <+> txt "{"
    <.> entryPointCall
    <.> txt "}"

/// Generate a C function "void init(void)" which initialises program counters
let internal mainInit ctx init compilations (entryCompilation: Compilation) =    
    txt "void" 
    <+> cpProgramName init 
    <+> txt "(void)"
    <+> txt "{"
    <.> ActivityTranslator.mainPCinit ctx compilations entryCompilation
    <.> txt "}"


let internal printState ctx printState entryCompilation = 
    let showPcs =
        entryCompilation.iface.pcs
        |> List.map (fun p -> translateQnameToGeneratedName p.name)
        |> List.map (fun pc -> "\\\"" + pc + """\" : %u""", pc)
        |> List.unzip
        |> (fun (ppList, argList) -> String.concat @",\n\t\t\t\t" ppList, String.concat ", " argList)
        |> (fun (a, b) -> sprintf """printf ("\t\t\t\"pcs\": {\n\t\t\t\t%s\n\t\t\t},\n", %s);""" a b)
        |> txt
    
    // show variables
    let showVars =
        let getFormatStrForArithmetic (dty: Types) =
            assert dty.IsPrimitive
            match dty with
            | Types.ValueTypes (BoolType) -> "%d"
            | Types.ValueTypes (FloatType FloatPrecision.Double)
            | Types.ValueTypes (FloatType FloatPrecision.Single) -> "%e"
            | Types.ValueTypes (IntType Int64) -> "%lld"
            | Types.ValueTypes (IntType Int32) -> "%ld"
            | Types.ValueTypes (IntType Int16) -> "%hd"
            | Types.ValueTypes (IntType Int8) -> "%hd" // should be hhd since C99
            | Types.ValueTypes (NatType Nat64) -> "%llu"
            | Types.ValueTypes (NatType Nat32) -> "%lu"
            | Types.ValueTypes (NatType Nat16) -> "%hu"
            | Types.ValueTypes (NatType Nat8) -> "%hu" // should be hhu since C99
            | _ -> failwithf "No format string for composite data type %A." dty

        let printPrimitive isLocal (n: TypedMemLoc) =
            let dty = getDatatypeFromTML ctx.tcc n
            match dty with
            | ValueTypes _ when dty.IsPrimitive ->
                let formStr = getFormatStrForArithmetic dty
                sprintf """printf("%s", %s);""" formStr (ppTml isLocal ctx n |> render None)
                //sprintf """printf("%s", %s);""" formStr (cpStateElement ctx n |> render None)
            | _ -> failwith "printPrimitive called on non-primitive."

        let rec printArray isLocal level (n: TypedMemLoc) =
            let ind = String.replicate level @"\t"
            let dty = getDatatypeFromTML ctx.tcc n
            match dty with
            | ValueTypes (ArrayType (size, _)) ->
                ([for i in [0..1..size-1] do 
                        let idx = { rhs = IntConst (System.Numerics.BigInteger i); typ = ValueTypes (IntType Int64) ; range = Range.range0}
                        yield sprintf """printf("%s");""" ind + (printAnything isLocal (level + 1) (TypedMemLoc.ArrayAccess (n, idx)))]
                 |> String.concat "\n\tprintf(\",\\n\");\n\t")
            | _ -> failwith "printArray called on non-array."

        and printStruct isLocal level (n: TypedMemLoc) =
            let ind = String.replicate level @"\t"
            let prefix x = "\\\"" + (x.basicId.ToString()) + """\" : """
            let dty = getDatatypeFromTML ctx.tcc n
            match dty with
            | ValueTypes (ValueTypes.StructType (_, _, fields)) ->
                let printField isLocal (v:VarDecl)  = 
                    sprintf """printf("%s");""" ind 
                    + sprintf """printf("%s");""" (prefix v.name) 
                    + printAnything isLocal (level + 1) (TypedMemLoc.FieldAccess (n, v.name.basicId))
                List.map (printField isLocal) fields 
                |> String.concat "\n\tprintf(\",\\n\");\n\t"
            | _ -> 
                failwith "printStruct called on non-struct."
        
        and printAnything isLocal level (n: TypedMemLoc) =
            let ind = String.replicate level @"\t"
            let dty = getDatatypeFromTML ctx.tcc n
            match dty with
            | ValueTypes _ when dty.IsPrimitive ->
                printPrimitive isLocal n
            | ValueTypes (ValueTypes.StructType _) ->
                sprintf """printf("{\n");"""
                + printStruct isLocal (level + 1) n
                + sprintf """printf("\n%s}");""" ind
            | ValueTypes (ArrayType _) ->
                sprintf """printf("[\n");"""
                + printArray isLocal (level + 1) n
                + sprintf """printf("\n%s]");""" ind
            | _ -> failwith "Only value types implemented."
            
        let rec printVar isLocal level (n: TypedMemLoc) (pos: Range.range) =
            // silently ignore if given tml is not in type check context
            // this happens for external prev variables that are added
            // as locals into the iface (after type checking)
            let ind = String.replicate level @"\t"
            let prefix = "\\\"" + (n.ToBasicString()) + "_line" + string(pos.StartLine) + """\" : """
            sprintf """printf("%s%s");""" ind prefix
            + printAnything isLocal level n    
                    
        let printParamDecl isLocal (p: ParamDecl) = 
            printVar isLocal 4 (Loc p.name) p.pos

        let vars = 
            [
                entryCompilation.iface.inputs |> List.map (printParamDecl false)
                entryCompilation.iface.outputs |> List.map (printParamDecl false)
                entryCompilation.iface.locals |> List.map (printParamDecl true) 
            ]
            |> List.concat
            |> List.filter (System.String.IsNullOrWhiteSpace >> not)
            
        match vars with
        | [] ->
            txt """printf ("\t\t\t\"vars\": {}\n");"""
        | vs ->
            """printf("\t\t\t\"vars\": {\n");"""
            + String.concat "\n\tprintf(\",\\n\");\n\t" vs
            + """printf("\n\t\t\t}\n");"""
            |> txt

    txt "void" 
    <+> cpProgramName printState
    <+> cpMainIface false entryCompilation.iface
    <+> txt "{"
    <.> (cpIndent (dpBlock [showPcs; showVars]))
    <.> txt "}"


let appMainLoop init tick printState entryCompilation =
    let initCall = 
        cpProgramName init
        <^> txt "()"
        <^> semi

    let tickCall = 
        cpProgramName tick
        <^> cpAppCall entryCompilation.iface
        <^> semi
        |> cpIndent

    let printStateCall =
        cpProgramName printState
        <^> cpAppCall entryCompilation.iface
        <^> semi
        |> cpIndent

    txt """ int main(void) {
    int running = 0; /* number of iterations */
    int bound = 60;
    printf("{\n\t\"trace\":[\n");
"""   
    <.> cpIndent initCall
    <.> txt """
    while( running < bound )
    {
        /* call tick function */
"""
    <.> cpIndent tickCall
    <.> txt """    
        /* display program state */
        printf ("\t\t{\n\t\t\t\"tick\": %i,\n", running);
"""
    <.> cpIndent printStateCall
    <.> txt """
        ++running;       
        running < bound?printf("\t\t},\n"):printf("\t\t}\n");
    }
    printf("\t]\n}");
    return 0; /* OK */
}"""


//=============================================================================
// Program Function prototypes: tick, init, printState
//=============================================================================

let programFunctionProtoype primitivePassByAddress name iface returns =
    cpType returns
    <+> cpProgramName name
    <+> cpMainIface primitivePassByAddress iface
    <^> semi
