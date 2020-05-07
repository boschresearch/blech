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

open Blech.Frontend.Constants
open Blech.Frontend.CommonTypes
open Blech.Frontend.BlechTypes  
open Blech.Frontend.PrettyPrint.DocPrint
open Blech.Frontend.TypeCheckContext

open Blech.Backend

open CPdataAccess2
open CPrinter


let private cpByPointer param = chr '*' <^> param

/// Inputs of the main functions 'tick' and 'init'
let private cpMainInputParam scalarPassByPointer (input: ParamDecl) =
    // determine whether it is a primitive value type or not
    txt "const"
    <+> match input.datatype with
        | ValueTypes (ArrayType _) ->
            cpArrayDeclDoc (Global input.name).Render input.datatype
        | ValueTypes typ when typ.IsPrimitive ->
            cpType input.datatype
            <+> if scalarPassByPointer then 
                    cpByPointer (Global input.name).Render
                else 
                    (Global input.name).Render
        | _ ->
            cpType input.datatype <+> cpDeref (txt "const" <+> (Global input.name).Render)


/// Outputs of the main functions 'tick' and 'init'. 
let private cpMainOutputParam (output: ParamDecl) =
    match output.datatype with
    | ValueTypes (ArrayType _) -> cpArrayDeclDoc (Global output.name).Render output.datatype
    | _ -> cpType output.datatype <+> cpDeref (Global output.name).Render
        

// translates the interface of the EntryPoint activity to C function interface for 'tick' and 'init'
let private cpMainIface scalarPassByPointer (iface: Compilation) =
    let cargs = 
        List.concat [
            iface.inputs |> List.map (cpMainInputParam scalarPassByPointer)
            iface.outputs |> List.map cpMainOutputParam
        ]
    (if List.isEmpty cargs then [txt "void"] else cargs)
    |> dpCommaSeparatedInParens


/// The following are specific functions to call the entry point activity from the tick function
/// They are called nowhere else

let private paramAsInput (p: ParamDecl) = 
    { rhs = RhsCur (TypedMemLoc.Loc p.name)
      typ = p.datatype
      range = p.pos }
let private paramAsOutput (p: ParamDecl) = 
    { lhs = LhsCur (TypedMemLoc.Loc p.name)
      typ = p.datatype
      range = p.pos }
/// Call to entry point activity
let private cpGlobalCall tcc primitivePassByAddress (iface: Compilation) =
    [
        if primitivePassByAddress then
            iface.inputs |> List.map (paramAsOutput >> cpOutputArg tcc >> getCExpr >> (fun x -> x.Render))
        else
            iface.inputs |> List.map (paramAsInput >> cpInputArg tcc >> getCExpr >> (fun x -> x.Render))
        iface.outputs |> List.map (paramAsOutput >> cpOutputArg tcc >> getCExpr >> (fun x -> x.Render))
        iface.actctx |> Option.toList |> List.map (fun _ -> txt "&blc_blech_ctx")
        iface.retvar |> Option.toList |> List.map (paramAsInput >> cpInputArg tcc >> getCExpr >> (fun x -> x.Render))
    ]
    |> List.concat
    |> dpCommaSeparatedInParens


/// Call parameters for the tick and the printState functions
/// To be used from the test app only

let internal cpAppCall tcc whoToCall (entryPointIface: Compilation) =
    let renderedCalleeName = (cpStaticName whoToCall)
    let renderedInputs = entryPointIface.inputs |> List.map (paramAsInput >> cpInputArg tcc)
    let renderedOutputs = entryPointIface.outputs |> List.map (paramAsOutput >> cpOutputArg tcc)
    let actCall = 
        [
            renderedInputs |> List.map (getCExpr >> (fun x -> x.Render))
            renderedOutputs |> List.map (getCExpr >> (fun x -> x.Render))
        ]
        |> List.concat
        |> dpCommaSeparatedInParens
        |> (<^>) renderedCalleeName
    let prereqStmts =
        [
            renderedInputs |> List.collect getPrereq
            renderedOutputs |> List.collect getPrereq
        ]
        |> List.concat
    prereqStmts @ [actCall <^> semi]
    |> dpBlock


/// Generate a C function "void tick(...)" which calls
/// enters the entry point activity in every tick.
let internal mainCallback tcc primitivePassByAddress tick entryName entryIface = 
    // Generates a c function call to the  EntryPoint activity
    let entryPointCall =
        cpStaticName entryName
        <^> cpGlobalCall tcc primitivePassByAddress entryIface 
        <^> semi
        |> cpIndent

    txt "void"
    <+> cpStaticName tick
    <+> cpMainIface primitivePassByAddress entryIface 
    <+> txt "{"
    <.> entryPointCall
    <.> txt "}"

/// Generate a C function "void init(void)" which initialises program counters
let internal mainInit ctx init (entryCompilation: Compilation) =    
    txt "void" 
    <+> cpStaticName init 
    <+> txt "(void)"
    <+> txt "{"
    <.> ActivityTranslator.mainPCinit ctx entryCompilation
    <.> txt "}"


let internal printState ctx printState (entryCompilation: Compilation) = 
    let showPcs =
        let rec getAllPcs pref actctx =
            actctx.subcontexts
            |> Seq.collect (fun kvp -> getAllPcs ((if pref.Equals "" then "" else pref + ".") + (kvp.Key |> fst) + "_" + (kvp.Key |> snd |> (renderCName Current ctx.tcc) |> render None)) kvp.Value)
            |> Seq.append (seq{pref, actctx.pcs})
        
        getAllPcs "" entryCompilation.GetActCtx
        |> Seq.map (fun (pref,tree) -> pref, PCtree.asList tree)
        |> Seq.collect (fun (pref,pc) -> pc |> List.map(fun p -> pref,p))
        |> Seq.toList
        |> List.map (fun (pref,pc) -> (if pref.Equals "" then "" else pref + ".") + pc.name.basicId)
        |> List.map (fun pc -> "\\\"" + pc + """\" : %u""", "blc_blech_ctx." + pc)
        |> List.unzip
        |> (fun (ppList, argList) -> String.concat @",\n\t\t\t\t" ppList, String.concat ", " argList)
        |> (fun (a, b) -> sprintf """printf ("\t\t\t\"pcs\": {\n\t\t\t\t%s\n\t\t\t},\n", %s);""" a b)
        |> txt
    
    // show variables
    let showVars =
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

        let printPrimitive isLocal prefStr (n: TypedMemLoc) =
            let dty = getDatatypeFromTML ctx.tcc n
            match dty with
            | ValueTypes _ when dty.IsPrimitive ->
                let formStr = getFormatStrForArithmetic dty
                sprintf """printf("%s", %s);""" formStr (prefStr + ((cpTml Current ctx.tcc n).Render |> render None))
            | _ -> failwith "printPrimitive called on non-primitive."

        let rec printArray isLocal level prefStr (n: TypedMemLoc) =
            let ind = String.replicate level @"\t"
            let dty = getDatatypeFromTML ctx.tcc n
            match dty with
            | ValueTypes (ArrayType (size, _)) ->
                ([for i in [SizeZero .. SizeOne .. size - SizeOne] do 
                        //let idx = { rhs = IntConst (System.Numerics.BigInteger i); typ = ValueTypes (IntType Int64) ; range = Range.range0}
                        let idx = { rhs = NatConst <| N64 i; typ = ValueTypes (NatType Nat64) ; range = Range.range0}
                        yield sprintf """printf("%s");""" ind + (printAnything isLocal (level + 1) prefStr (TypedMemLoc.ArrayAccess (n, idx)))]
                 |> String.concat "\n\tprintf(\",\\n\");\n\t")
            | _ -> failwith "printArray called on non-array."

        and printStruct isLocal level prefStr (n: TypedMemLoc) =
            let ind = String.replicate level @"\t"
            let prefix x = "\\\"" + (x.basicId.ToString()) + """\" : """
            let dty = getDatatypeFromTML ctx.tcc n
            match dty with
            | ValueTypes (ValueTypes.StructType (_, _, fields)) ->
                let printField isLocal (v:VarDecl)  = 
                    sprintf """printf("%s");""" ind 
                    + sprintf """printf("%s");""" (prefix v.name) 
                    + printAnything isLocal (level + 1) prefStr (TypedMemLoc.FieldAccess (n, v.name.basicId))
                List.map (printField isLocal) fields 
                |> String.concat "\n\tprintf(\",\\n\");\n\t"
            | _ -> 
                failwith "printStruct called on non-struct."
        
        and printAnything isLocal level prefStr (n: TypedMemLoc) =
            let ind = String.replicate level @"\t"
            let dty = getDatatypeFromTML ctx.tcc n
            match dty with
            | ValueTypes _ when dty.IsPrimitive ->
                printPrimitive isLocal prefStr n
            | ValueTypes (ValueTypes.StructType _) ->
                sprintf """printf("{\n");"""
                + printStruct isLocal (level + 1) prefStr n
                + sprintf """printf("\n%s}");""" ind
            | ValueTypes (ArrayType _) ->
                sprintf """printf("[\n");"""
                + printArray isLocal (level + 1) prefStr n
                + sprintf """printf("\n%s]");""" ind
            | _ -> failwith "Only value types implemented."
            
        let rec printVar isLocal level prefStr (n: TypedMemLoc) (pos: Range.range) =
            // silently ignore if given tml is not in type check context
            // this happens for external prev variables that are added
            // as locals into the iface (after type checking)
            let ind = String.replicate level @"\t"
            let prefix = "\\\"" + (n.ToBasicString()) + "_line" + string(pos.StartLine) + """\" : """
            sprintf """printf("%s%s");""" ind prefix
            + printAnything isLocal level prefStr n    
                    
        let printParamDecl isLocal prefStr (p: ParamDecl) = 
            printVar isLocal 4 prefStr (TypedMemLoc.Loc p.name) p.pos

        let vars = 
            let rec getAllLocals pref actctx =
                actctx.subcontexts
                |> Seq.collect (fun kvp -> getAllLocals ((if pref.Equals "" then "" else pref + ".") + (kvp.Key |> fst) + "_" + (kvp.Key |> snd |> (renderCName Current ctx.tcc) |> render None)) kvp.Value)
                |> Seq.append (seq{pref, actctx.locals})
            
            let allLocals =
                getAllLocals "" entryCompilation.GetActCtx
                |> Seq.collect (fun (pref,locals) -> locals |> List.map(fun p -> pref,p))
                |> Seq.toList
                |> List.map (fun (pref,local) -> (if pref.Equals "" then "" else pref + "."), local)
                |> List.unzip
                
            [
                entryCompilation.inputs |> List.map (printParamDecl false "")
                entryCompilation.outputs |> List.map (printParamDecl false "")
                allLocals ||> List.map2 (printParamDecl true)
            ]
            |> List.concat
            |> List.filter (System.String.IsNullOrWhiteSpace >> not)
            
        match vars with
        | [] ->
            txt """printf ("\t\t\t\"vars\": {}\n");"""
        | vs ->
            // the generated variable access will -> into the context but here the context is give as a value directly
            // so we rewrite all -> into .
            // yes this is a temprorary hack
            let vs = vs |> List.map(fun s -> s.Replace(CTX+"->", CTX+"."))
            """printf("\t\t\t\"vars\": {\n");"""
            + String.concat "\n\tprintf(\",\\n\");\n\t" vs
            + """printf("\n\t\t\t}\n");"""
            |> txt

    txt "void" 
    <+> cpStaticName printState
    <+> cpMainIface false entryCompilation
    <+> txt "{"
    <.> (cpIndent (dpBlock [showPcs; showVars]))
    <.> txt "}"

let appMainLoop ctx init tick printState entryCompilation =
    let initCall = 
        cpStaticName init
        <^> txt "()"
        <^> semi

    let tickCall = 
        cpAppCall ctx.tcc tick entryCompilation
        |> cpIndent

    let printStateCall =
        cpAppCall ctx.tcc printState entryCompilation
        |> cpIndent

    if ctx.cliContext.trace then
        txt """int main(void) {
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
    else
        txt """int main(void) {
    int running = 0; /* number of iterations */
    int bound = 60;
"""
        <.> cpIndent initCall
        <.> txt """
    while( running < bound )
    {
        /* call tick function */
"""
        <.> cpIndent tickCall
        <.> txt """
        ++running;
    }
    return 0; /* OK */
}"""


//=============================================================================
// Program Function prototypes: tick, init, printState
//=============================================================================

let programFunctionProtoype primitivePassByAddress name iface returns =
    cpType returns
    <+> cpStaticName name
    <+> cpMainIface primitivePassByAddress iface
    <^> semi
