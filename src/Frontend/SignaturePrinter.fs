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

namespace Blech.Frontend

module SignaturePrinter =

    open Blech.Common
    open Blech.Common.PPrint
    
    open Constants
    open CommonTypes
    open DocPrint
    
    // Abbreviations
    module Scope = SymbolTable.Scope

    let bpGeneratedComment info =
        txt "/*"
        <.> txt "**" <+> info
        <.> txt "*/"

    // ----------------------------------------------
    // Functions for printing blech code form an AST    
    // naming: bp<ASTNode> which means: blech print <ASTNode>   
    // ----------------------------------------------
    
    
    let bpLineDoc comment = 
        txt "///" <^> txt comment

    let bpBlockDoc comment =
        txt "/**" <^> txt comment <^> txt "*/"

    // Helper functions, specific for printing the untyped AST
    let bpBitVec (unsigned: bigint) prefix =
        let s = 
            match prefix with
            | 'x' ->
                (unsigned.ToString "X").TrimStart [|'0'|]  // remove leading 0s from bigint representation
            | 'o' ->
                let octs = seq {
                    let mutable n = unsigned
                    while not n.IsZero do
                        yield string (n % 8I)
                        n <- n / 8I
                }
                Seq.foldBack (fun s o -> o + s) octs ""
            | _ ->  // prefix = 'b'
                let bits = seq {
                    let mutable n = unsigned
                    while not n.IsZero do
                        if n.IsEven then yield '0' else yield '1'
                        n <- n >>> 1
                }
                Array.ofSeq bits |> Array.rev |> System.String
            
        sprintf "0%c%s" prefix s |> txt


    let bpLiteral = function 
                | AST.Bool (value = true) ->
                    txt "true"
                | AST.Bool (value = false) ->
                    txt "false"
                | AST.String (value = text) ->
                    txt text
                    |> dpString
                | AST.MultiLineString (value = text) ->
                    text.Split BlechString.Linefeed
                    |> Seq.map txt
                    |> dpMultiLineString
                | AST.Int (value = i) ->
                    string i |> txt
                | AST.Bits (value = lit) ->
                    match lit with
                    | BAny (_, repr) -> txt repr
                    | _ -> failwith "A bits literal should always have a representation"
                | AST.Float (value = lit) ->
                    match lit with
                    | FAny (_, Some repr) -> txt repr
                    | _ -> failwith "A float literal should always have a represention"

    let rec bpAttribute attr =
        let ppKey = function
            | AST.Quoted (text=k) -> txt k |> dquotes
            | AST.Ident (text=k) -> txt k
            
        match attr with
        | AST.Key (key, _) ->
            ppKey key
        | AST.KeyValue (key, value, _) ->
            ppKey key <+> chr '=' <+> bpLiteral value
        | AST.Structured (key, attrs, _) ->
            ppKey key <+> 
            ( List.map bpAttribute attrs 
              |> punctuate comma
              |> vsep
              |> align
              |> parens )
              
    let bpAnnotation (anno: AST.Annotation) =
        match anno.Attribute with
        | AST.KeyValue (AST.Ident(text=Attribute.Key.linedoc), AST.Literal.String(value=comment), _) ->
            bpLineDoc comment
        | AST.KeyValue (AST.Ident(text=Attribute.Key.blockdoc), AST.Literal.String(value=comment), _) ->
            bpBlockDoc comment
        | attr ->
            dpAnnotation <| bpAttribute attr        


    let bpPragma (pragma: AST.Annotation) = 
        dpPragma <| bpAttribute pragma.Attribute
        

    let bpOptAnnotations (annos: AST.Annotation list) =
        match annos with
        | [] ->
            None
        | _ ->
            Seq.map bpAnnotation annos 
            |> dpToplevelClose 
            |> Some        

    // Variable declaration related functions
    let private bpTypeAnnotation = function 
        | None -> empty
        | Some doc -> chr ':' <+> doc


    let private bpInitValue prefix = function
        | None -> prefix
        | Some doc -> prefix <+> chr '=' <.> doc


    let private bpName name = txt <| string name
    
    
    let private bpStaticNamedPath (snp : AST.StaticNamedPath) =
        List.map bpName snp.path
        |> punctuate dot
        |> hcat

   
    let private bpUnitExpr uexpr = 
        txt "UnitExpr"

    let private bpOptUnit optUnit = 
        match optUnit with
        | None -> empty
        | Some u -> bpUnitExpr u |> brackets


    
    // ---  built-in types

    let private bpNaturalType = function
        | Nat8 -> txt "nat8"
        | Nat16 -> txt "nat16"
        | Nat32 -> txt "nat32"
        | Nat64 -> txt "nat64"
    

    let private bpIntegerType = function
        | IntType.Int8 -> txt "int8"
        | IntType.Int16 -> txt "int16"
        | IntType.Int32 -> txt "int32"
        | IntType.Int64 -> txt "int64"


    let private bpBitvecType = function
        | Bits8 -> txt "bits8"
        | Bits16 -> txt "bits16"
        | Bits32 -> txt "bits32"
        | Bits64 -> txt "bits64"
    

    let private bpFloatType = function            
        | FloatType.Float32 -> txt "float32"
        | FloatType.Float64 -> txt "float64"
      

    let private bpTemporalQualifier = function
        | AST.TemporalQualification.Current -> 
            empty
        | AST.TemporalQualification.Previous _ -> 
            txt "prev" <^> space
        | AST.TemporalQualification.Next _ -> 
            txt "next" <^> space


    let private bpPermission (permission: AST.Permission) = 
        match permission with
        | AST.Permission.ReadOnly (ro = ro) ->
            match ro with
            | AST.Immutable.Let -> txt "let"
            | AST.Immutable.Const -> txt "const"
            | AST.Immutable.Param -> txt "param"
        | AST.Permission.ReadWrite (rw = rw) ->
            match rw with
            | AST.Mutable.Var -> txt "var"


    // --- members
    
    // 

    let rec bpStaticVarDecl (vd: AST.VarDecl) =
        let datatype = Option.map bpDataType vd.datatype
        let initValue = Option.map bpExpr vd.initialiser
        
        let varDecl =
            bpPermission vd.permission <+> bpName vd.name <^> 
            (bpTypeAnnotation datatype 
             |> bpInitValue <| initValue 
             |> gnest dpTabsize) 

        let optExtern =
            if vd.isExtern then Some <| txt "extern" else None    
        
        bpOptAnnotations vd.annotations
        |> dpOptLinePrefix
        <| dpOptSpacePrefix optExtern varDecl

    // enum type declaration
    
    and private bpEnumRawType = function
        | None -> empty
        | Some datatype -> chr ':' <+> bpDataType datatype
        
    and private bpEnumRawValue = function 
        | None -> empty
        | Some staticExpr -> chr '=' <.> bpExpr staticExpr

    and private bpEnumIsDefault = function
        | false -> empty
        | true -> txt "default"

    and private bpTagDecl (td: AST.TagDecl) =
        dpName td.name <+> bpEnumRawValue td.rawvalue <+> bpEnumIsDefault td.isDefault
        |> gnest dpTabsize
        
    and bpEnumTypeDecl optExtensionDocs (et : AST.EnumTypeDecl) =
        let optRef = 
            if et.isReference then Some <| txt "ref" else None

        let optExt =
            match optExtensionDocs with
            | None ->
                txt "end"
            | Some extDocs ->
                txt "extension"
                <.> ( extDocs
                      |> vsep
                      |> indent dpTabsize )
                <.> txt "end"

        let enumDecl =
            txt "enum"
            <+> dpName et.name
            <^> bpEnumRawType et.rawtype
            <.> indent dpTabsize (List.map bpTagDecl et.tags |> vsep)
            // extensions are preliminaryfor now
            <.> optExt

        bpOptAnnotations et.annotations 
        |> dpOptLinePrefix
        <| dpOptSpacePrefix optRef enumDecl 

    // struct type declaration

    and private bpDynamicMember (dm : AST.Member) = 
        match dm with
        | AST.Member.Var vd ->
            let datatype = Option.map bpDataType vd.datatype
            let initValue = Option.map bpExpr vd.initialiser        
            let varDecl =
                bpPermission vd.permission <+> bpName vd.name <^> 
                (bpTypeAnnotation datatype 
                 |> bpInitValue <| initValue 
                 |> gnest dpTabsize) 

            bpOptAnnotations vd.annotations
            |> dpOptLinePrefix
            <| varDecl
        | _ ->
            failwith "Unexpected dynamic member"


    and bpStructTypeDecl optExtensionDocs (st : AST.StructTypeDecl) =
        let optRef = 
            if st.isReference then Some <| txt "ref" else None

        let optExt =
            match optExtensionDocs with
            | None ->
                txt "end"
            | Some extDocs ->
                txt "extension"
                <.> ( extDocs
                      |> vsep
                      |> indent dpTabsize )
                <.> txt "end"

        let structDecl =
            txt "struct"
            <+> dpName st.name
            <.> indent dpTabsize (List.map bpDynamicMember st.fields |> vsep)
            // extensions are preliminaryfor now
            <.> optExt

        bpOptAnnotations st.annotations 
        |> dpOptLinePrefix
        <| dpOptSpacePrefix optRef structDecl

    // typealias declaration

    and bpTypeAliasDecl (ta : AST.TypeAliasDecl) =
        let optRef =
            if ta.isReference then Some <| txt "ref" else None
            
        let typealiasDecl = 
            txt "typealias"
            <+> dpName ta.name
            <+> (chr '=' <.> bpDataType ta.aliasfor
                 |> gnest dpTabsize)

        bpOptAnnotations ta.annotations 
        |> dpOptLinePrefix
        <| dpOptSpacePrefix optRef typealiasDecl
        

    // --- data types

    and private bpArrayLength expr =
        bpExpr expr

    and private bpOptDataType optTyp = 
        match optTyp with
        | None -> empty
        | Some dty -> bpDataType dty


    and private bpDataType typ =     
        match typ with
        //| VoidType -> txt "void"
        | AST.BoolType _ -> txt "bool"
        | AST.BitvecType (size, _) -> 
            bpBitvecType size 
        | AST.NaturalType (size, optUnit, _) -> 
            bpNaturalType size <^> bpOptUnit optUnit
        | AST.IntegerType (size, optUnit, _) ->
            bpIntegerType size <^> bpOptUnit optUnit
        | AST.FloatType (precision, optUnit, _) ->
            bpFloatType precision <^> bpOptUnit optUnit
        | AST.ArrayType (length, arrType, _) -> 
            (bpArrayLength length |> brackets) <^> bpDataType arrType 
        | AST.SliceType (dty, _) ->
            (empty |> brackets) <^> bpDataType dty 
        | AST.Signal (dtyOpt, _) ->
            (bpOptDataType dtyOpt |> group) <+> txt "signal"
        | AST.TypeName tn ->
            bpStaticNamedPath tn

    

    and private bpAccess = function
        | AST.Access.Name n ->
            bpName n
        | AST.Access.Point (id = n) ->
            chr '.' <^> bpName n
        | AST.Access.Index (index = expr) ->
            bpExpr expr |> brackets
        | AST.Access.StaticIndex (index = expr) ->
            chr '.' <^> bpExpr expr |>  brackets
        
    and private bpAccessList path =
        path
        |> List.map bpAccess
        |> List.fold (<^>) empty
        
    and private bpDynamicAccessPath (loc: AST.DynamicAccessPath) = 
        bpTemporalQualifier loc.timepoint <^> bpAccessList loc.path
      
    

    // --- expressions

    and private bpOptExpr optExpr = 
        match optExpr with
        | None -> Empty
        | Some expr -> bpPrecExpr dpPrec.["min"] expr

    and private bpExpr (expr: AST.Expr)  = 
        bpPrecExpr dpPrec.["min"] expr

    and private bpLexpr = function
        | AST.LhsInAssignment.Wildcard _ -> 
            txt "_"
        | AST.LhsInAssignment.Loc l -> 
            bpDynamicAccessPath l    
            
    and private bpStructField name value =
        bpName name <+> chr '=' <+> bpExpr value


    and private bpWithOptIndex suffix = function 
        | None ->
            suffix
        | Some index ->
            (bpExpr index
                |> brackets) <+> chr '=' <+> suffix
        
    and private bpArrayField index value =
        index |> bpWithOptIndex (bpExpr value) 
        
    
    and private bpSubProgramCall pName inputs optOutputs =
        let progName = 
            match pName with
            | AST.Code.Procedure dynPath -> 
                bpDynamicAccessPath dynPath
        progName <^> 
        (inputs |> dpCommaSeparatedInParens
            |> dpOptArguments <| optOutputs
            |> align
            |> group)

    and private bpPrecExpr outerPrec (expr: AST.Expr) =
        match expr with
        | AST.Expr.Const c ->
            bpLiteral c
        | AST.Expr.AggregateConst (fieldExpr, _) ->
            let fields = 
                match fieldExpr with
                | AST.FieldExpr.ResetFields -> 
                    [empty]
                | AST.FieldExpr.StructFields sfs -> 
                    sfs |> List.map (fun sf -> bpStructField sf.name sf.expr)
                | AST.FieldExpr.ArrayFields afs -> 
                    afs |> List.map (fun af -> bpArrayField af.index af.value)
            fields
            |> dpCommaSeparatedInBraces
            |> align
            |> group
        | AST.Expr.SliceConst (indexOpt, lenOpt, buf, _) ->
            bpOptExpr indexOpt <^> chr ',' <+> bpOptExpr lenOpt
            |> brackets
            |> (</>) <| bpDynamicAccessPath buf
            |> align
            |> group                     
        // --- variable
        | AST.Expr.Var access ->
            bpDynamicAccessPath access 
        // --- function call
        | AST.Expr.FunctionCall (fp, inputs, optOutputs, _)->
            bpSubProgramCall fp 
            <| List.map bpExpr inputs
            <| List.map bpDynamicAccessPath optOutputs
        // --- logical operators ---
        | AST.Expr.Not (expr, _) -> 
            fun p -> txt "not" <+> bpPrecExpr p expr
            |> dpPrecedence outerPrec dpPrec.["not"]
        | AST.Expr.And (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "and" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["and"]
        | AST.Expr.Or (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "or" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["or"]
        // --- arithmetic operators
        | AST.Expr.Add (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "+" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["+"]
        | AST.Expr.Sub (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "-" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["-"]
        | AST.Expr.Mul (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "*" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["*"]
        | AST.Expr.Div (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "/" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["/"]
        | AST.Expr.Mod (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "%" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["%"]
        | AST.Expr.Pow (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "**" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["**"]
        | AST.Expr.Unm (expr, _) ->
            fun p -> txt "-" <^> bpPrecExpr p expr
            |> dpPrecedence outerPrec dpPrec.["unary"]
        // --- comparison operators
        | AST.Expr.Eq (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "==" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["=="]
        | AST.Expr.Ieq (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "!=" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["!="]
        | AST.Expr.Les (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "<" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["<"]
        | AST.Expr.Leq (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "<=" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["<="]
        | AST.Expr.Grt (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt ">" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.[">"]
        | AST.Expr.Geq (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt ">=" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.[">="]            
        // --- identity operators
        | AST.Expr.Ideq (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "==" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["==="]
        | AST.Expr.Idieq (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "!=" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["!=="]
        // -- bitwise operators
        | AST.Expr.Band (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "&" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["&"]
        | AST.Expr.Bor (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "|" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["|"]
        | AST.Expr.Bxor (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "^" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["^"]
        | AST.Expr.Shl (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "<<" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["<<"]
        | AST.Expr.Shr (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt ">>" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.[">>"]
        | AST.Expr.Bnot (expr, _) ->
            fun p -> txt "~" <+> bpPrecExpr p expr
            |> dpPrecedence outerPrec dpPrec.["~"]
        // -- advanced bitwise operators
        | AST.Expr.Sshr (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "+>>" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["+>>"]
        | AST.Expr.Rotl (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "<<>" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["<<>"]
        | AST.Expr.Rotr (lhs, rhs) ->
            fun p -> bpPrecExpr p lhs <.> txt "<>>" <+> bpPrecExpr p rhs
            |> dpPrecedence outerPrec dpPrec.["<>>"]
        // --- type conversion
        | AST.Expr.Convert (expr, dataType, behaviour) ->
            fun p -> bpPrecExpr p expr <+> txt ("as" + string behaviour) <.> bpDataType dataType
            |> dpPrecedence outerPrec dpPrec.["as"]
        // --- type annotation
        | AST.Expr.HasType (expr, dataType) ->
            fun p -> bpPrecExpr p expr <+> txt ":" <.> bpDataType dataType
            |> dpPrecedence outerPrec dpPrec.[":"]
        // -- operators on arrays and slices --
        | AST.Expr.Len (expr, _) ->
            fun p -> txt "#" <+> bpPrecExpr p expr
            |> dpPrecedence outerPrec dpPrec.["#"]
        | AST.Expr.Cap (expr, _) ->
            fun p -> txt "##" <+> bpPrecExpr p expr
            |> dpPrecedence outerPrec dpPrec.["##"]
        // -- parentheses --
        | AST.Expr.Parens (expr, _) ->
            fun p -> txt "(" <^> bpPrecExpr p expr <^> txt ")"
            |> dpPrecedence outerPrec dpPrec.["parens"]


    let private bpParamDecl (param: AST.ParamDecl) =
            bpName param.name 
            <^> chr ':'
            <+> bpDataType param.datatype


    let private bpOptReturns prefix optReturns =
        match optReturns with
        | None -> prefix
        | Some doc -> prefix <.> doc

    
    let private bpOutputs prefix outputs =
        match outputs with
        | [] -> 
            prefix
        | outputs ->
            prefix <.> dpArguments outputs


    let private bpReturnDecl (ret: AST.ReturnDecl) = 
            let ref = 
                if ret.isReference then txt "ref" <+> empty 
                else empty
            let sharing =
                match ret.sharing with
                | [] -> 
                    empty 
                | ns -> 
                    txt "shares"             
                    <+> (List.map bpName ns
                         |> dpCommaSeparated)
                    <+> empty
            let dty = 
                bpDataType ret.datatype

            txt "returns" <+> ref <^> sharing <^> dty


    let bpExternalFunction (ef: AST.Prototype) =
        assert ef.isExtern
        assert ef.isFunction

            
        let inputs = List.map bpParamDecl ef.inputs
        let outputs = List.map bpParamDecl ef.outputs
        let optReturns = Option.map bpReturnDecl ef.result

        let externPrototype =
            txt "extern" <+> txt "function" <+> bpName ef.name <^>
                (dpArguments inputs
                |> bpOutputs <| outputs
                |> bpOptReturns <| optReturns
                |> align
                |> group) 

        bpOptAnnotations ef.annotations
        |> dpOptLinePrefix
        <| externPrototype



    /// Prints the blech source code for a signature file from namechecking lookuptable and an AST
    let printSignature (ctx : ExportInference.ExportContext) (ast : AST.CompilationUnit) =
        assert ast.IsModule // only modules have signatures

        // ----------------------------------------------
        // Functions for printing signature code form an AST    
        // naming: ps<ASTNode> which means: print signature <ASTNode>   
        // ----------------------------------------------

        let psAbstractType annotations abstractType isRef (name: Name) =
            let optAnnos = 
                bpOptAnnotations annotations
            let abstractKind = 
                match abstractType with
                | OpaqueInference.Simple -> Attribute.SimpleType.ToDoc
                | OpaqueInference.Array -> Attribute.OpaqueArray.ToDoc
                | OpaqueInference.Struct -> Attribute.OpaqueStruct.ToDoc
            let optRef =
                if isRef then Some <| txt "ref" else None
                
            txt "type" <+> dpName name
            |> dpOptSpacePrefix optRef
            |> dpOptLinePrefix (Some abstractKind)
            |> dpOptLinePrefix optAnnos

        let psIdentifier (id : Identifier) = 
            txt <| string id

        let psLongIdentifier (su : LongIdentifier) =
            List.map psIdentifier su
            |> punctuate dot
            |> hcat

        //let psSingletonUsage (su: ExportInference.SingletonUsage) = 
        //    List.map psLongIdentifier su

        let psSingletonSignature (singletonSig: ExportInference.SingletonSignature) =
            let usedSingletons = 
                match singletonSig with
                | ExportInference.Opaque su
                | ExportInference.Translucent su ->
                    if List.isEmpty su then None
                    else List.map psLongIdentifier su
                         |> dpCommaSeparatedInBrackets
                         |> Some

            txt "singleton"
            |> dpOptSpacePostfix <| usedSingletons
            
        
        let psPrototype isFunction name inputs outputs result =
            let subprog = if isFunction then txt "function" else txt "activity"
            let inputs = List.map bpParamDecl inputs
            let outputs = List.map bpParamDecl outputs
            let optReturns = Option.map bpReturnDecl result

            subprog <+> bpName name <+>
            (dpArguments inputs
                |> bpOutputs <| outputs
                |> bpOptReturns <| optReturns
                |> align
                |> group) 


        let psSubProgram (sp: AST.SubProgram) =
            let optAnnos = bpOptAnnotations sp.annotations
            
            dpOptLinePrefix optAnnos
            <| psPrototype sp.isFunction sp.name sp.inputs sp.outputs sp.result


        let psSingletonSubProgram (singletonSig : ExportInference.SingletonSignature) (sp: AST.SubProgram) = 
            // printfn "Singleton Signature for sub program: %A\n Singleton Signature %A" sp.name singletonSig
            let optAnnos = bpOptAnnotations sp.annotations
            let singleton = psSingletonSignature singletonSig
            let prototype = psPrototype sp.isFunction sp.name sp.inputs sp.outputs sp.result

            dpOptLinePrefix optAnnos
            <| ( singleton <.> prototype
                 |> align 
                 |> group )


        let psSingletonExternalFunction (singletonSig : ExportInference.SingletonSignature) (pt: AST.Prototype) = 
            let optAnnos = bpOptAnnotations pt.annotations
            let singleton = psSingletonSignature singletonSig
            let prototype = psPrototype true pt.name pt.inputs pt.outputs pt.result

            dpOptLinePrefix optAnnos
            <| ( txt "extern" <.> singleton <.> prototype 
                 |> align
                 |> group )


        let psOpaqueSingletonSignature annotations (singletonSig : ExportInference.SingletonSignature) (name: Name)  = 
            let optAnnos = bpOptAnnotations annotations

            dpOptLinePrefix optAnnos
            <| ( psSingletonSignature singletonSig <+> dpName name
                 |> align
                 |> group )


        let psExtensionMember (mbr: AST.Member) =
            match mbr with
            | AST.Member.Subprogram sp ->
                psSubProgram sp
            | AST.Member.TypeAlias ta ->
                bpTypeAliasDecl ta
            | _ ->
                failwith "Extensions are preliminary and only used to test implicit member access"


        let psOptExtensions (extensionMembers: AST.Member list) = 
            match extensionMembers with
            | [] -> 
                None
            | mbrs ->
                List.map psExtensionMember mbrs
                |> Some 
            
            
        let psStructTypeDecl (st: AST.StructTypeDecl) =
            psOptExtensions st.members
            |> bpStructTypeDecl <|st


        let psEnumTypeDecl (st: AST.EnumTypeDecl) =
            psOptExtensions st.members
            |> bpEnumTypeDecl <|st


        let psMember (mbr : AST.Member) =
            
            match mbr with
            | AST.Member.EnumType et -> 
                if ctx.IsExported et.name then 
                    if ctx.IsOpaqueType et.name then
                        let absType = Option.get <| ctx.TryGetOpaqueType et.name
                        psAbstractType et.annotations absType et.isReference et.name 
                    else
                        psEnumTypeDecl et 
                else empty  
            
            | AST.Member.StructType st ->
                if ctx.IsExported st.name then 
                    if ctx.IsOpaqueType st.name then
                        let absType = Option.get <| ctx.TryGetOpaqueType st.name
                        psAbstractType st.annotations absType st.isReference st.name 
                    else 
                        psStructTypeDecl st
                else empty  

            | AST.Member.TypeAlias ta ->
                if ctx.IsExported ta.name then 
                    if ctx.IsOpaqueType ta.name then
                        let absType = Option.get <| ctx.TryGetOpaqueType ta.name
                        psAbstractType ta.annotations absType ta.isReference ta.name 
                    else 
                        bpTypeAliasDecl ta
                else empty  
                
            | AST.Member.OpaqueType ot ->
                failwith "this should not occur"
            
            | AST.Member.Var vdecl ->
                if ctx.IsExported vdecl.name then 
                    bpStaticVarDecl vdecl
                else empty

            | AST.Member.Subprogram sp ->
                if ctx.IsExported sp.name then
                    if ctx.HasOpaqueSingletonSignature sp.name then
                        psOpaqueSingletonSignature sp.annotations (ctx.GetSingletonSignature sp.name) sp.name
                    elif ctx.HasTranslucentSingletonSignature sp.name then
                        psSingletonSubProgram (ctx.GetSingletonSignature sp.name) sp
                    else
                        psSubProgram sp
                else empty

            | AST.Member.Prototype pt ->
                if ctx.IsExported pt.name then
                    if ctx.HasOpaqueSingletonSignature pt.name then
                        psOpaqueSingletonSignature pt.annotations (ctx.GetSingletonSignature pt.name) pt.name
                    elif ctx.HasTranslucentSingletonSignature pt.name then
                        psSingletonExternalFunction (ctx.GetSingletonSignature pt.name) pt
                    else
                        bpExternalFunction pt
                else empty

            | AST.Member.OpaqueSingleton os ->
                // Used to group external functions that change the same C object
                psOpaqueSingletonSignature os.annotations (ctx.GetSingletonSignature os.name) os.name
                // failwith "Opaque signatures are not part of module implementations, which are printed here."
            
            | AST.Member.Unit u ->
                empty
                // bpUnitDecl u
            
            | AST.Member.Clock c ->
                empty
                // bpClockDecl c
            
            | AST.Member.Pragma p ->
                empty
            
            | AST.Member.Nothing -> 
                failwith "this should have been removed"


        let psImportExposes (exposing: AST.Exposing) =
            let requiredExposedNames =
                List.filter ctx.IsRequiredImport exposing.names

            if List.isEmpty requiredExposedNames then
                empty
            else
                txt "exposes" <.> 
                ( List.map dpName requiredExposedNames
                  |> dpRemoveEmpty
                  |> dpCommaSeparated )
                |> align
                |> group
            
        let psImport (imp: AST.Import) = 
            let requiredExposedNames = 
                Option.map psImportExposes imp.exposing

            if ctx.IsRequiredImport imp.localName  then
                (if imp.isInternal then txt "import internal" else txt "import") 
                <+> dpModuleName imp.localName
                <+> dquotes imp.modulePath.path.ToDoc
                |> dpOptSpacePostfix <| requiredExposedNames   
            else empty

        let psModuleSpec (ms: AST.ModuleSpec) =
            let optAnnos = 
                bpOptAnnotations ms.annotations
            let spec = 
                if ms.isInternal then txt "internal signature" else txt "signature"

            dpOptLinePrefix optAnnos spec

        let generatedCode =
            bpGeneratedComment <| txt "This is generated code - do not touch!"

        let imports = 
            List.map psImport ast.imports
            |> dpRemoveEmpty
            |> dpToplevelClose

        let spec = 
            assert (Option.isSome ast.moduleSpec)
            psModuleSpec <| Option.get ast.moduleSpec
            
        let members = 
            List.map psMember ast.members
            |> dpRemoveEmpty
            |> dpToplevel
        
        [generatedCode; imports; spec ; members]
        |> dpRemoveEmpty
        |> dpToplevel
        |> render (Some 80)

