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

open Blech.Frontend.Constants
open Blech.Frontend.CommonTypes
open Blech.Frontend.BlechTypes  
open Blech.Frontend.PrettyPrint.DocPrint
open Blech.Frontend.TypeCheckContext

open Blech.Backend

open CPdataAccess2
open CPrinter


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
        iface.actctx |> Option.toList |> List.map (fun _ -> txt "&blc_blech_ctx")
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

open Blech.Frontend
let rec private ppTopLevelArgument (tcc: TypeCheckContext) = function
    | TypedMemLoc.Loc qname ->
        // cannot simply use getValueFromName because of primitive-pass-by-value special case
        let result = BLC + "_" + qname.basicId |> txt
        let typeAndIsOutput =
            match tcc.nameToDecl.TryGetValue qname with
            | true, Declarable.ParamDecl p -> Some p.datatype, p.isMutable
            | _ -> None, false
        let needDeref = false
        // if given qname is an input AND primitive AND primitive pass by address is true 
        let needDeref = 
            needDeref
            || match typeAndIsOutput with
               | Some t, true when t.IsPrimitive && tcc.cliContext.passPrimitiveByAddress -> true
               | _ -> false
        // if given qname is an output AND primitive
        let needDeref = 
            needDeref
            || match typeAndIsOutput with
               | Some t, true when t.IsPrimitive-> true
               | _ -> false
        // or given qname is a struct 
        let needDeref = 
            needDeref
            || match fst typeAndIsOutput with
               | Some (ValueTypes (ValueTypes.StructType _)) -> true
               | _ -> false
        // then dereference
        if needDeref then
            txt "(*" <^> result <^> txt")"
        // otherwise just print the name
        else
            result
    | TypedMemLoc.FieldAccess (subtml, ident) ->
        (ppTopLevelArgument tcc subtml) <^> dot <^> txt ident
    | TypedMemLoc.ArrayAccess (subtml, idx) ->
        let {prereqStmts=preStmts; cExpr=idxDoc} = cpExpr tcc idx
        preStmts @ [(ppTopLevelArgument tcc subtml) <^> (brackets idxDoc.Render)]
        |> dpBlock
    
let ppTml isLocal ctx (tml: TypedMemLoc) = 
    if isLocal then
        BLC + "_" + tml.ToUnderscoreString() |> txt
    else
        ppTopLevelArgument ctx tml

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
                sprintf """printf("%s", %s);""" formStr (prefStr + (ppTml isLocal ctx.tcc n |> render None))
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
                getAllLocals "blc_blech_ctx" entryCompilation.GetActCtx
                |> Seq.collect (fun (pref,locals) -> locals |> List.map(fun p -> pref,p))
                |> Seq.toList
                |> List.map (fun (pref,local) -> (if pref.Equals "" then "" else pref + "."), local)
                |> List.unzip
                
            [
                entryCompilation.inputs |> List.map (printParamDecl false "")
                entryCompilation.outputs |> List.map (printParamDecl false "")
                allLocals ||> List.map2 (printParamDecl true) |> List.map(fun s -> s.Replace(CTX+"->", CTX+"."))
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
            //let vs = vs |> List.map(fun s -> s.Replace(CTX+"->", CTX+"."))
            """printf("\t\t\t\"vars\": {\n");"""
            + String.concat "\n\tprintf(\",\\n\");\n\t" vs
            + """printf("\n\t\t\t}\n");"""
            |> txt

    txt "void" 
    <+> cpStaticName printState
    <+> cpMainIface ctx.tcc false entryCompilation
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

let programFunctionPrototype tcc primitivePassByAddress name iface returns =
    cpType returns
    <+> cpStaticName name
    <+> cpMainIface tcc primitivePassByAddress iface
    <^> semi
