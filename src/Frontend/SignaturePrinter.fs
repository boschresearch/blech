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
    open PrettyPrint.DocPrint
    

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
                    txt text |> dquotes
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
            ppKey key <+>
            (chr '=' <.> bpLiteral value |> gnest dpTabsize)
        | AST.Structured (key, attrs, _) ->
            ppKey key <^> 
            (
            (List.map (fun a -> bpAttribute a) attrs) 
                |> dpCommaSeparatedInParens
                |> align
                |> group)
        
    let private bpAnnotation (anno: AST.Annotation) =
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


    let private bpName name = txt <| name.ToString()
    
    
    let private bpStaticNamedPath path =
        List.map (fun (n: Name) -> txt <| n.idToString) path
        |> punctuate dot
        |> hcat

   
    let private bpUnitExpr uexpr = 
        txt "UnitExpr"

    let private bpOptUnit optUnit = 
        match optUnit with
        | None -> empty
        | Some u -> bpUnitExpr u |> brackets


    
    // --- types

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


    let rec private bpArrayLength expr =
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
        | AST.TypeName name ->
            bpStaticNamedPath name.path

    

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
            
    and private ppStructField name value =
        bpName name <+> chr '=' <+> bpExpr value


    and private ppWithOptIndex suffix = function 
        | None ->
            suffix
        | Some index ->
            (bpExpr index
                |> brackets) <+> chr '=' <+> suffix
        
    and private ppArrayField index value =
        index |> ppWithOptIndex (bpExpr value) 
        
    
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
                    sfs |> List.map (fun sf -> ppStructField sf.name sf.expr)
                | AST.FieldExpr.ArrayFields afs -> 
                    afs |> List.map (fun af -> ppArrayField af.index af.value)
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
        | AST.Expr.ImplicitMember name ->
            chr '.' <^> bpStaticNamedPath name.path
        // --- variable
        | AST.Expr.Var access ->
            bpDynamicAccessPath access 
        // --- function call
        | AST.Expr.FunctionCall (fp, inputs, optOutputs, _)->
            bpSubProgramCall fp 
            <| List.map (fun e -> bpExpr e) inputs
            <| List.map (fun e -> bpDynamicAccessPath e) optOutputs
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


    let private bpOptReturns prefix = function
        | None -> prefix
        | Some doc -> prefix <.> doc
    
    
    let private bpReturnDecl (ret: AST.ReturnDecl) = 
            // TODO: improve formatting for missing ref and sharing - now creates blanks because of <+>, fjg 24.01.19    
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
                |> dpOptArguments <| outputs
                |> bpOptReturns <| optReturns
                |> align
                |> group) 

        bpOptAnnotations ef.annotations
        |> dpOptLinePrefix
        <| externPrototype


    let bpPermission (permission: AST.Permission) = 
        match permission with
        | AST.Permission.ReadOnly (ro = ro) ->
            match ro with
            | AST.Immutable.Let -> txt "let"
            | AST.Immutable.Const -> txt "const"
            | AST.Immutable.Param -> txt "param"
            // | Input -> txt "input"
        | AST.Permission.ReadWrite (rw = rw) ->
            match rw with
            | AST.Mutable.Var -> txt "var"
            // | Output -> txt "output"



    /// Prints the blech source code for a signature file from namechecking lookuptable and an AST
    let printSignature (lut: SymbolTable.LookupTable) (ast: AST.Package) =
        assert (Option.isSome ast.spec )                // only modules have signatures
        assert (ast.loadWhat = Package.Implementation)  // interfaces do not have signatures 


        // ----------------------------------------------
        // Functions for printing signature code form an AST    
        // naming: ps<ASTNode> which means: print signature <ASTNode>   
        // ----------------------------------------------

        let psSpec lut (spec : AST.ModuleSpec) =
            txt "signature" <+> bpStaticNamedPath spec.path
        
        let psSubProgram (sp: AST.SubProgram) =
            let subprog =
                if sp.isFunction then
                    txt "function"
                else    
                    txt "activity"
            
            let inputs = List.map bpParamDecl sp.inputs
            let outputs = List.map bpParamDecl sp.outputs
            let optReturns = Option.map bpReturnDecl sp.result

            let prototype = 
                subprog <+> bpName sp.name <^>
                (dpArguments inputs
                 |> dpOptArguments <| outputs
                 |> bpOptReturns <| optReturns
                 |> align
                 |> group) 

            bpOptAnnotations sp.annotations
            |> dpOptLinePrefix
            <| prototype
           
        let psStaticVarDecl (vd: AST.VarDecl) =
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

        // TODO: check exposedness, fjg 25.01.19
        let psMember lut (mbr: AST.Member) =
            match mbr with
            | AST.Member.Subprogram subProg ->
                psSubProgram subProg
            | AST.Member.Prototype protoTyp ->
                bpExternalFunction protoTyp
            | AST.Member.Var vdecl when vdecl.permission.IsStatic ->
                psStaticVarDecl vdecl
            | AST.Member.Pragma p ->
                bpPragma p
            | _ ->
                empty

        let imports = List.map (psMember lut) ast.imports
        let spec = Option.get ast.spec |> psSpec lut
        let members = List.map (psMember lut) ast.members
        
        (imports @ spec :: members)
        |> dpToplevel
        |> render (Some 80)

