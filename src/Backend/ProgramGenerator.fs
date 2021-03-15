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

/// This module contains all functionality which generates the main loop
/// and printState function for testing (tracing) Blech code.

[<RequireQualifiedAccess>]
module Blech.Backend.ProgramGenerator

open Blech.Common
open Blech.Common.PPrint
open Blech.Common.Range

open Blech.Frontend.BlechTypes  
open Blech.Frontend.PrettyPrint.DocPrint

open Blech.Backend

open CPdataAccess2
open CPrinter


let private ctxByAddr = "&" + CTX


/// Inputs of the main functions 'tick' and 'init'
let private cpMainInputParam tcc scalarPassByPointer (input: ParamDecl) =
    let paramName = input.name |> renderCName Current tcc
    // determine whether it is a primitive value type or not
    txt "const"
    <+> match input.datatype with
        | ValueTypes (ArrayType _) ->
            cpArrayDeclDoc paramName input.datatype
        | ValueTypes typ when typ.IsPrimitive ->
            cpType input.datatype
            <+> if scalarPassByPointer then 
                    cpDeref paramName
                else 
                    paramName
        | _ ->
            cpType input.datatype <+> cpDeref (txt "const" <+> paramName)


/// Outputs of the main functions 'tick' and 'init'. 
let private cpMainOutputParam tcc (output: ParamDecl) =
    let paramName = output.name |> renderCName Current tcc
    match output.datatype with
    | ValueTypes (ArrayType _) -> cpArrayDeclDoc paramName output.datatype
    | _ -> cpType output.datatype <+> cpDeref paramName
        

// translates the interface of the EntryPoint activity to C function interface for 'tick' and 'print'
let private cpMainIface tcc scalarPassByPointer (iface: Compilation) =
    let cargs = 
        List.concat [
            iface.inputs |> List.map (cpMainInputParam tcc scalarPassByPointer)
            iface.outputs |> List.map (cpMainOutputParam tcc)
            iface.retvar |> Option.toList |> List.map (cpMainOutputParam tcc)
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
        iface.actctx |> Option.toList |> List.map (fun _ -> txt ctxByAddr)
        if primitivePassByAddress then
            iface.inputs |> List.map (paramAsOutput >> cpOutputArg tcc >> getCExpr >> (fun x -> x.Render))
        else
            iface.inputs |> List.map (paramAsInput >> cpInputArg tcc >> getCExpr >> (fun x -> x.Render))
        iface.outputs |> List.map (paramAsOutput >> cpOutputArg tcc >> getCExpr >> (fun x -> x.Render))
        iface.retvar |> Option.toList |> List.map (paramAsOutput >> cpOutputArg tcc >> getCExpr >> (fun x -> x.Render))
    ]
    |> List.concat
    |> dpCommaSeparatedInParens


/// Call parameters for the tick and the printState functions
/// To be used from the test app only

let internal cpAppCall tcc whoToCall (entryPointIface: Compilation) =
    let addAmp pe =
            match getCExpr pe with
            | Blob cPath -> cPath.PrependAddrOf |> Blob
            | x -> x // impossible, a lhs cannot be a complex expression or just a value
    let procIn (t, pe) =
        match t with
        | ValueTypes (ValueTypes.StructType _) ->
            addAmp pe
        | _ -> getCExpr pe
    let procOut (t, pe) =
        match t with
        | ValueTypes (ValueTypes.ArrayType _) -> getCExpr pe
        | _ -> addAmp pe
    let renderedCalleeName = (cpStaticName whoToCall)
    let renderedInputs = entryPointIface.inputs |> List.map (paramAsInput >> (fun i -> i.typ, cpInputArg tcc i))
    let renderedOutputs = entryPointIface.outputs |> List.map (paramAsOutput >> (fun o -> o.typ, cpOutputArg tcc o))
    // create dummy receiver for return value if entry point returns something
    let receiverPrereqStmt, renderedReceiver =
        match entryPointIface.retvar with
        | None ->
            [empty], []
        | Some r ->
            // calle does return something but no receiver var has been specified (_)
            // create dummy receiver variable
            let lhsName = mkIndexedAuxQNameFrom "receiverVar"
            let lhsTyp = r.datatype
            let tmpDecl = cpArrayDeclDoc (renderCName Current tcc lhsName) lhsTyp <^> semi
            let v = 
                { 
                    VarDecl.pos = range0
                    name = lhsName
                    datatype = lhsTyp
                    mutability = Mutability.Variable
                    initValue = {rhs = NatConst <| Nat.Zero8; typ = ValueTypes (NatType Nat8); range = range0} // that is a dummy/garbage
                    annotation = Blech.Frontend.Attribute.VarDecl.Empty
                    allReferences = System.Collections.Generic.HashSet() 
                }
            Blech.Frontend.TypeCheckContext.addDeclToLut tcc lhsName (Blech.Frontend.Declarable.VarDecl v)
            let tmpLhs = 
                {lhs = LhsCur (TypedMemLoc.Loc lhsName); typ = lhsTyp; range = range0} // range0 since it does not exist in original source code
                |> (fun o -> o.typ, cpOutputArg tcc o)
            [tmpDecl], [tmpLhs]
        
        
    let actCall = 
        [
            renderedInputs |> List.map (procIn >> (fun x -> x.Render))
            renderedOutputs |> List.map (procOut >> (fun x -> x.Render))
            renderedReceiver |> List.map (procOut >> (fun x -> x.Render))
        ]
        |> List.concat
        |> dpCommaSeparatedInParens
        |> (<^>) renderedCalleeName
    let prereqStmts =
        [
            renderedInputs |> List.collect (snd >> getPrereq)
            renderedOutputs |> List.collect (snd >> getPrereq)
            receiverPrereqStmt
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
    <+> cpMainIface tcc primitivePassByAddress entryIface 
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

/// This generates the entry point state printer which calls the actual
/// printers generated in TraceGenerator.fs
let internal printState ctx printState (entryCompilation: Compilation) = 
    let showPcs =
        let args =
            [ txt TraceGenerator.emptyCString
              txt ctxByAddr ]
            |> dpCommaSeparatedInParens
        cpStaticName entryCompilation.name <^> txt TraceGenerator.printPcSuffix <^> args <^> semi

    let showVars =
        let argOfInput (i: ParamDecl) =
            {
                rhs = RhsCur (TypedMemLoc.Loc i.name)
                typ = i.datatype
                range = i.pos
            }
        let argOfOutput (i: ParamDecl) =
            {
                lhs = LhsCur (TypedMemLoc.Loc i.name)
                typ = i.datatype
                range = i.pos
            }
        let args =
            [ [txt TraceGenerator.emptyCString]
              [txt ctxByAddr]
              entryCompilation.inputs |> List.map (argOfInput >> cpInputArg ctx.tcc >> (fun x -> x.Render))
              entryCompilation.outputs |> List.map (argOfOutput >> cpOutputArg ctx.tcc >> (fun x -> x.Render))
              ]
            |> List.concat
            |> dpCommaSeparatedInParens
        cpStaticName entryCompilation.name <^> txt TraceGenerator.printLocalsSuffix <^> args <^> semi
        
    txt "void" 
    <+> cpStaticName printState
    <+> cpMainIface ctx.tcc false entryCompilation
    <+> txt "{"
    <.> txt """printf("\t\t\t\"pcs\": {");"""
    <.> cpIndent showPcs
    <.> txt """printf("\n\t\t\t},\n");"""
    <.> txt """printf("\t\t\t\"vars\": {");"""
    <.> cpIndent showVars
    <.> txt """printf("\n\t\t\t}\n");"""
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

let programFunctionPrototype tcc primitivePassByAddress name iface returns =
    cpType returns
    <+> cpStaticName name
    <+> cpMainIface tcc primitivePassByAddress iface
    <^> semi
