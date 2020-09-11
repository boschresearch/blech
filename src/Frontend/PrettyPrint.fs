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

/// Uses nuget Package: https://github.com/polytypic/PPrint

module PrettyPrint =

    /// Constants and functions which are shared among different
    /// pretty printing modules (below).
    
    module DocPrint =
        open Blech.Common.PPrint

        let dpTabsize = 4

        let dpIndent = 
            indent dpTabsize
        
        /// Operator precedence mapping
        let dpPrec = 
            Map.ofList [ 
                ("min", 0); 
                (":", 5); ("as", 5);
                ("or", 10);
                ("and", 20);
                ("<", 30); ("<=", 30); (">", 30); (">=", 30); ("==", 30); ("!=", 30); ("===", 30); ("!==", 30)
                ("|", 40);
                ("^", 50); ("#", 50); ("##", 50); // TODO: stimmt das?
                ("&", 60);
                ("<<", 70); (">>", 70); ("+>>", 70); ("<>>", 70); ("<<>", 70); 
                ("+", 80); ("-", 80);
                ("*", 90); ("/", 90); ("%", 90);
                ("unary", 100); ("not", 100); ("~", 100);
                ("**", 110);
                ("max", 1000); ("parens", 1000) // TODO: stimmt das?
                ]      
        
        
        // Expression related functions
        let private precParens outerPrec docPrec doc =
            if outerPrec > docPrec then
                doc |> parens
            else 
                doc 

        let dpPrecedence outerPrec prec fdoc =
                (fdoc prec
                |> align)
                |> precParens outerPrec prec
                |> group

 
        // Functions for printing a list of things (comma separated with/without some brackets)
        
        
        let dpCommaSeparated docs = 
            docs
            |> punctuate comma
            |> vsep
            |> align
            |> group 


           
        let private _dpCommaSeparatedInBrackets withBrackets docs =
            docs
            |> punctuate comma
            |> vsep
            |> align
            |> withBrackets
            |> group        

        let dpCommaSeparatedInParens = _dpCommaSeparatedInBrackets parens
        let dpCommaSeparatedInBraces = _dpCommaSeparatedInBrackets braces
        let dpCommaSeparatedInBrackets : (Doc list -> Doc) = _dpCommaSeparatedInBrackets brackets

        let dpToplevelClose docs =
            docs
            |> vsep
            //|> align
            //|> group

        let dpOptLinePrefix (optDoc: Doc option) doc =
            match optDoc with
            | Some od ->
                od <.> doc
            | None ->
                doc

        let dpOptSpacePrefix (optDoc: Doc option) doc =
            match optDoc with
            | Some prfx ->
                prfx <+> doc
            | None ->
                doc

        /// Convert any object with a ToString representation to a Doc
        let dpName name = txt <| name.ToString()

        let dpToplevel elements =
            elements
            |> punctuate line
            |> vsep

        let dpRemoveEmptyLines elements =
            elements
            |> Seq.filter (function
                | Empty -> false // remove empty documents from sequence
                | _ -> true)

        /// statement blocks (body of a control-flow structure)
        /// removes empty lines
        let dpBlock : Doc seq -> Doc =
            dpRemoveEmptyLines >> vsep

        // Printing of argument lists in particular
        let dpArguments = dpCommaSeparatedInParens


        let dpOptArguments prefix = function
            | [] -> 
                prefix
            | outputs -> 
                prefix <..> dpArguments outputs

        // Printing concurrentcy control flow blocks in particular
        let dpStrength = function
            | CommonTypes.Weak -> txt "weak"
            | CommonTypes.Strong -> empty
        
        let dpCobeginBlock (strength, block) =   
            txt "cobegin" <+> dpStrength strength <.>
            (dpBlock block
                |> indent dpTabsize)
        
        let dpWithBlock (strenght, block) =
            txt "with" <+> dpStrength strenght <.>
            (dpBlock block
                |> indent dpTabsize)
                  
        let dpCobegin = function
            | cobeginBlock :: withBlocks -> 
                (dpCobeginBlock cobeginBlock ::
                    List.map (fun wb -> dpWithBlock wb) withBlocks
                    |> vsep) <.>
                txt "end"
            | [] -> empty // never executed
    
        // Preemptions        
        let dpPreemption = function
            | CommonTypes.Abort ->
                txt "abort"
            | CommonTypes.Reset ->
                txt "reset"
            | CommonTypes.Suspend ->
                txt "suspend"

        let dpMoment = function 
            | CommonTypes.After ->
                txt "after"
            | CommonTypes.Before ->
                txt "before"
            | CommonTypes.OnNext -> 
                txt "next"

        let dpAliasedType = function
            | None -> empty
            | Some doc -> chr '=' <.> doc

        // Variable declaration related functions
        let dpTypeAnnotation = function 
            | None -> empty
            | Some doc -> chr ':' <+> doc

        let dpInitValue prefix = function
            | None -> prefix
            | Some doc -> prefix <+> chr '=' <.> doc

    
        let dpCall name arguments = 
            name <^> 
            (arguments |> dpArguments
                |> align
                |> group)


        // Printing of Blech subprogram calls
        let dpBlechCall name inputs optOutputs =
            name <^> 
            (inputs |> dpArguments
                |> dpOptArguments <| optOutputs
                |> align
                |> group)


        // Printing an annotation
        let dpAnnotation attribute =               // TODO: move this and functions from Signature printer to Blech printer, fjg 18.02.19
            chr '@' <^> brackets attribute


        // Printing a pragma - scope level annotation
        let dpPragma attribute =
            txt "@@" <^> brackets attribute


    module ASTPrint =
        
        open System.Numerics

        open Blech.Common.PPrint
    
        open DocPrint
        open Constants
        open CommonTypes
        open AST
    
    
        let pprint (node: AST.ASTNode) =

            let refFExpr = ref (fun e -> empty)  // tricky forward declaration
                
            // Helper functions, specific for printing the untyped AST
            let ppStaticNamedPath path =
                List.map (fun (n: Name) -> txt <| n.idToString) path
                |> punctuate dot
                |> hcat

            let ppTemporalQualifier = function
                | Current -> empty
                | Previous _ -> txt "prev" <^> space
                | Next _ -> txt "next" <^> space

            let ppAccess = function
                | Name n ->
                    dpName n
                | Point (id = n) ->
                    chr '.' <^> dpName n
                | Index (index = expr) ->
                    !refFExpr expr |> brackets
                | StaticIndex (index = expr) ->
                    chr '.' <^> !refFExpr expr |>  brackets
                
            let ppAccessList path =
                path
                |> List.map ppAccess
                |> List.fold (<^>) empty
        
            let ppDynamicAccessPath timePoint path = 
                ppTemporalQualifier timePoint <^> ppAccessList path
            
            // define what to do with the individual AST nodes

            let fNothing = txt @"/* nothing */"

            let fPackage (_, optSpec, members) = 
                let docs = 
                    match optSpec with
                    | Some spec ->
                        txt "module" :: members
                    | None ->
                        members 
                docs
                |> punctuate line 
                |> vsep

            let fMember = id

            let fStmt = id

            let ppConditions = function
                | [] -> empty //cannot happen
                | [oneCond] -> oneCond
                | manyConds -> dpCommaSeparatedInParens manyConds
        
            let fAssign (_, lefthandSide, righthandSide) =
                lefthandSide <+> 
                (chr '=' <.> righthandSide
                 |> gnest dpTabsize)

            let ppOptMsg prefix = function
                | None -> prefix
                | Some msg -> 
                  prefix <+> msg

            let fAssert (_, conds, msg) = 
                txt "assert" <+> ppConditions conds
                |> ppOptMsg <| msg

            let fAssume (_, conds, msg) = 
                txt "assume" <+> ppConditions conds
                |> ppOptMsg <| msg

            let fAwait (_, conds) = 
                txt "await" <+> ppConditions conds 

            let ppOptElse = function 
                | [] -> 
                    txt "end"
                | bodyElse -> 
                    txt "else" <.> 
                    (dpBlock bodyElse
                     |> indent dpTabsize) <.>
                    txt "end"

            let fITE (_, conds, bodyThen, bodyElse, isElseIf) =
                txt "if" <+> ppConditions conds <+> txt "then" <.>
                (dpBlock bodyThen
                 |> indent dpTabsize) <.>
                (if isElseIf then 
                    txt "else" <^> 
                    dpBlock bodyElse 
                 else
                    ppOptElse bodyElse)

            let ppOptWhere prefix = function
                | None ->
                    prefix
                | Some boolExpr ->
                    prefix <.> txt "where" <+> boolExpr
                    |> gnest dpTabsize 
    
            let ppCase (pattern, optWhere, block) =
                txt "case" <+> pattern
                |> ppOptWhere <| optWhere <.>
                (dpBlock block
                 |> indent dpTabsize)
                 
            let fMatch (_, expr, cases) =
                txt "match" <+> expr <.>
                (List.map (fun c -> ppCase c) cases
                 |> vsep) <.>
                txt "end"
         
            let fCobegin (_, blocks) = 
                dpCobegin blocks

            let fWhile (_, conds, body) =
                txt "while" <+> ppConditions conds <+> txt "repeat" <.>
                (dpBlock body
                 |> indent dpTabsize) <.>
                txt "end"
                
            let fRepeat (_, body, conds) =
                txt "repeat" <.>
                (dpBlock body
                 |> indent dpTabsize) <.>
                match conds with
                | [] -> txt "end"
                | cs -> txt "until" <+> ppConditions cs <+> txt "end"
        
            let ppStep = function
                | None -> empty
                | Some doc -> chr ',' <.> doc

            let fNumericFor (_, var, init, limit, optStep, body) =
                txt "for" <+> var <+> 
                (chr '=' <.> init <^> chr ',' <.> limit <^> ppStep optStep
                 |> gnest dpTabsize) <+> 
                txt "do" <.>
                (dpBlock body
                 |> indent dpTabsize) <.>
                txt "end"
         
            let ppIterator = function
                | In -> txt "in"
                | Of -> txt "of"

            let fIteratorFor (_, iterator, var, iterable, body) = 
                txt "for" <+> var <+> 
                (ppIterator iterator <.> iterable
                 |> gnest dpTabsize) <+>
                 txt "do" <.>
                 (dpBlock body
                  |> indent dpTabsize) <.>
                 txt "end"

            let fPreempt (_, preemption, conds, moment, body) =
                dpPreemption preemption <+> txt "when" <+> ppConditions conds <+> dpMoment moment <.>
                (dpBlock body
                 |> indent dpTabsize) <.>
                txt "end"

            let fSubScope (_, block) =
                txt "do" <.>
                (dpBlock block
                 |> indent dpTabsize) <.>
                txt "end"

            let ppSubProgramCall pName inputs optOutputs =
                let progName = 
                    match pName with
                    | Procedure dynPath -> 
                        ppDynamicAccessPath dynPath.timepoint dynPath.path
                progName <^> 
                (inputs |> dpCommaSeparatedInParens
                 |> dpOptArguments <| optOutputs
                 |> align
                 |> group)

            let fActCall (_, optReceiver, pName, inputs, optOutputs) = 
                match optReceiver with
                | None -> 
                    txt "run"
                | Some (Text "return") ->
                    txt "return run"
                | Some rcvr ->
                    txt "run" <+> rcvr <+> chr '='
                <.> (ppSubProgramCall pName inputs optOutputs) 
                |> gnest dpTabsize

            let fFunCall (_, pName, inputs, optOutputs) =
                ppSubProgramCall pName inputs optOutputs 
            
            let ppOptPayload = ppOptMsg

            let fEmit (_, receiver, optPayload) =
                txt "emit" <+> receiver <+> ppOptPayload (txt "=") optPayload
                
            let fReturn (_, exprOpt) = 
                let expr = match exprOpt with | None -> empty | Some e -> e
                txt "return" <+> expr

            let ppPermission = function
                | AST.ReadOnly (ro = ro) ->
                    match ro with
                    | Let -> txt "let"
                    | Immutable.Const -> txt "const"
                    | Param -> txt "param"
                    // | Input -> txt "input"
                | ReadWrite (rw = rw) ->
                    match rw with
                    | Mutable.Var -> txt "var"
                    // | Output -> txt "output"
        
            let fVarDecl (_, name, permission, datatype, initValue, annotations) = 
                ppPermission permission <+> dpName name <^> 
                (dpTypeAnnotation datatype 
                 |> dpInitValue <| initValue 
                 |> gnest dpTabsize) 

            let fParamDecl (_, name, _, datatype) =
                dpName name <^> chr ':' <+> datatype

            let fUnitDecl _ = empty
            let fClockDecl _ = empty
        
            let fImport _ = empty

            let fUnitExpr uexpr = txt "UnitExpr"

            let ppOptUnit = function
                | None -> empty
                | Some u -> fUnitExpr u |> brackets

            // --- types
            let ppIntegerType = function
                | IntType.Int8 -> txt "int8"
                | IntType.Int16 -> txt "int16"
                | IntType.Int32 -> txt "int32"
                | IntType.Int64 -> txt "int64"

            let ppNaturalType = function
                | Nat8 -> txt "nat8"
                | Nat16 -> txt "nat16"
                | Nat32 -> txt "nat32"
                | Nat64 -> txt "nat64"
    
            let ppBitvecType = function
                | Bits8 -> txt "bits8"
                | Bits16 -> txt "bits16"
                | Bits32 -> txt "bits32"
                | Bits64 -> txt "bits64"
        

            let ppFloatType = function            
                | FloatType.Float32 -> txt "float32"
                | FloatType.Float64 -> txt "float64"
                  
            let ppArrayLength = !refFExpr 

            let rec ppDataTypes datatypes =
                List.map (fun dt -> fDataType dt) datatypes 
            
            and ppInputTypes inputs =
                ppDataTypes inputs 
                |> dpCommaSeparatedInParens
 
            and ppOptOutputTypes prefix = function
                | [] -> prefix
                | datatypes -> prefix <..> ppInputTypes datatypes

            and ppReturnTypes prefix = function
                | [] -> prefix
                //| datatype :: [] -> prefix <.> txt "->" <+> fDataType datatype
                | datatypes -> prefix <.> txt "->" <^> (ppDataTypes datatypes
                                                        |> dpCommaSeparatedInParens)

            and ppOptDataType = function
                | None -> empty
                | Some dty -> fDataType dty
            

            and fDataType typ =     
                match typ with
                //| VoidType -> txt "void"
                | BoolType _ -> txt "bool"
                | BitvecType (size, _) ->
                    ppBitvecType size
                | NaturalType (size, optUnit, _) -> 
                    ppNaturalType size <^> ppOptUnit optUnit
                | IntegerType (size, optUnit, _) ->
                    ppIntegerType size <^> ppOptUnit optUnit
                | FloatType (precision, optUnit, _) ->
                    ppFloatType precision <^> ppOptUnit optUnit
                | ArrayType (length, arrType, _) -> 
                    (ppArrayLength length |> brackets) <^> fDataType arrType 
                | SliceType (dty, _) ->
                    (empty |> brackets) <^> fDataType dty 
                | Signal (dtyOpt, _) ->
                    (ppOptDataType dtyOpt |> group) <+> txt "signal"
                | TypeName name ->
                    ppStaticNamedPath name.path
                
            let fReturnDecl (_, isRef, sharing, dtyDoc) =
                let isRefDoc = if isRef then txt "ref" else empty
                let sharingDoc =
                    match sharing with
                    | [] -> empty 
                    | ns -> 
                        List.map dpName ns
                        |> dpCommaSeparatedInParens
                        |> (<+>) (txt "sharing")
                txt "returns" <+> isRefDoc <+> sharingDoc <+> dtyDoc

            let ppReturns prefix = function
            | None -> prefix
            | Some doc -> prefix <.> doc

            let fSubProgram (_, isFunction, name, inputs, outputs, resOpt, body, annons) =
                let prefix =
                    if isFunction then
                        txt "function"
                    else    
                        txt "activity"
                ( annons 
                  //|> punctuate line 
                  |> vsep )
                <.> prefix <^> dpName name <^>
                (dpArguments inputs
                 |> dpOptArguments <| outputs
                 |> ppReturns <| resOpt
                 |> align
                 |> group) 
                <.> (body |> vsep |> indent dpTabsize) 
                <.> txt "end"

            let fFunctionPrototype (_, name, inputs, outputs, resOpt, annons) =
                ( annons 
                  //|> punctuate line 
                  |> vsep )
                <.> txt "function" <^> dpName name <^>
                (dpArguments inputs
                 |> dpOptArguments <| outputs
                 |> ppReturns <| resOpt
                 |> align
                 |> group) 

            // --- Expressions ---

            let ppLexpr l = ppDynamicAccessPath l.timepoint l.path 
            let fLexpr access = 
                match access with
                | Wildcard _ -> txt "_"
                | Loc l -> ppLexpr l
            
            let ppBitVec (unsigned: bigint) prefix =
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

            let rec ppStructField name value =
                dpName name <+> chr '=' <+> fExpr value

            and ppWithOptIndex suffix = function 
                | None ->
                    suffix
                | Some index ->
                    (fExpr index
                     |> brackets) <+> chr '=' <+> suffix
        
            and ppArrayField index value =
                index |> ppWithOptIndex (fExpr value) 

            and ppLiteral = function 
                | Bool (value = true) ->
                    txt "true"
                | Bool (value = false) ->
                    txt "false"
                | String (value = text) ->
                    txt text |> dquotes
                | Bits (value = bits) ->
                    match bits with
                    | BAny (_, repr) -> txt repr
                    | _ -> failwith "A bits literal should always have a representation"
                | Int (value = i) ->
                    string i |> txt
                | Float (value = lit) ->
                    match lit with
                    | FAny (_, Some repr) -> txt repr
                    | _ -> failwith "A float literal should always have a represention"
            and ppOptExpr = function
                | None -> Empty
                | Some e -> fExpr e
            and ppExpr outerPrec = function
                | Const c ->
                    ppLiteral c
                | AggregateConst (fieldExpr, _) ->
                    match fieldExpr with
                    | ResetFields -> [empty]
                    | StructFields sfs -> sfs |> List.map (fun sf -> ppStructField sf.name sf.expr)
                    | ArrayFields afs -> afs |> List.map (fun af -> ppArrayField af.index af.value)
                    |> dpCommaSeparatedInBraces
                    |> align
                    |> group
                | SliceConst (indexOpt, lenOpt, buf, _) ->
                    ppOptExpr indexOpt <^> chr ',' <+> ppOptExpr lenOpt
                    |> brackets
                    |> (</>) <| ppLexpr buf
                    |> align
                    |> group                     
                | ImplicitMember name ->
                    chr '.' <^> ppStaticNamedPath name.path
                // --- variable
                | Var access ->
                    ppDynamicAccessPath access.timepoint access.path  
                // --- function call
                | Expr.FunctionCall (fp, inputs, optOutputs, _)->
                    ppSubProgramCall fp 
                    <| List.map (fun e -> fExpr e) inputs
                    <| List.map (fun e -> ppLexpr e) optOutputs
                // --- logical operators ---
                | Not (expr, _) -> 
                    fun p -> txt "not" <+> ppExpr p expr
                    |> dpPrecedence outerPrec dpPrec.["not"]
                | And (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "and" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["and"]
                | Or (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "or" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["or"]
                // --- arithmetic operators
                | Add (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "+" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["+"]
                | Sub (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "-" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["-"]
                | Mul (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "*" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["*"]
                | Div (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "/" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["/"]
                | Mod (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "%" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["%"]
                | Pow (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "**" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["**"]
                | Unm (expr, _) ->
                    fun p -> txt "-" <^> ppExpr p expr
                    |> dpPrecedence outerPrec dpPrec.["unary"]
                // --- comparison operators
                | Eq (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "==" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["=="]
                | Ieq (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "!=" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["!="]
                | Les (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "<" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["<"]
                | Leq (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "<=" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["<="]
                | Grt (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt ">" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.[">"]
                | Geq (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt ">=" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.[">="]            
                // --- identity operators
                | Ideq (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "===" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["==="]
                | Idieq (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "!==" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["!=="]
                // -- bitwise operators
                | Band (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "&" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["&"]
                | Bor (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "|" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["|"]
                | Bxor (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "^" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["^"]
                | Shl (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "<<" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["<<"]
                | Shr (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt ">>" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.[">>"]
                | Bnot (expr, _) ->
                    fun p -> txt "~" <+> ppExpr p expr
                    |> dpPrecedence outerPrec dpPrec.["~"]
                | Sshr (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "+>>" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["+>>"]
                | Rotl (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "<<>" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["<<>"]
                | Rotr (lhs, rhs) ->
                    fun p -> ppExpr p lhs <.> txt "<>>" <+> ppExpr p rhs
                    |> dpPrecedence outerPrec dpPrec.["<>>"]
                // --- type conversion
                | Convert (expr, dataType, behaviour) ->
                    fun p -> ppExpr p expr <+> txt ("as" + string behaviour) <.> fDataType dataType
                    |> dpPrecedence outerPrec dpPrec.["as"]
                // --- type annotation
                | HasType (expr, dataType) ->
                    fun p -> ppExpr p expr <+> txt ":" <.> fDataType dataType
                    |> dpPrecedence outerPrec dpPrec.[":"]
                // -- operators on arrays and slices --
                | Len (expr, _) ->
                    fun p -> txt "#" <+> ppExpr p expr
                    |> dpPrecedence outerPrec dpPrec.["#"]
                | Cap (expr, _) ->
                    fun p -> txt "##" <+> ppExpr p expr
                    |> dpPrecedence outerPrec dpPrec.["##"]
                // -- parentheses --
                | Parens (expr, _) ->
                    fun p -> txt "(" <^> ppExpr p expr <^> txt ")"
                    |> dpPrecedence outerPrec dpPrec.["parens"]

            and fExpr expr =
                ppExpr dpPrec.["min"] expr

            refFExpr := fExpr  // before doing anything supply the refernce

            // --- Receiver

            let fReceiver = function    
                | Location lhs -> 
                    fLexpr lhs
                | FreshLocation vdecl -> 
                    ppPermission vdecl.permission
                    <+> dpName vdecl.name
                | ReturnLocation _ ->
                    txt "return"

            // --- Conditions

            let fCondition = function
                | Cond expr -> fExpr expr
                | SignalBinding vdecl ->
                    ppPermission vdecl.permission
                    <+> if vdecl.isReference then txt "ref" else empty
                    <+> dpName vdecl.name
                    <+> dpTypeAnnotation (Option.map fDataType vdecl.datatype)
                    <+> chr '='
                    <+> Option.get (Option.map fExpr vdecl.initialiser) // grammar ensures there must be Some expr here
                | Tick (spath, _) ->
                    txt "tick" <+> ppStaticNamedPath spath.path
        
            let ppEnumRawType = function
                | None -> empty
                | Some datatype -> chr ':' <+> datatype
        
            let ppEnumRawValue = function 
                | None -> empty
                | Some staticExpr -> chr '=' <.> fExpr staticExpr

            let ppEnumIsDefault = function
                | false -> empty
                | true -> txt "default"

            let fTagDecl (td: TagDecl) =
                dpName td.name <+> ppEnumRawValue td.rawvalue <+> ppEnumIsDefault td.isDefault
                |> gnest dpTabsize
        
            let fEnumTypeDecl (_, isRef, name, rawtypeDoc, tagsDoc, membersDoc, annonsDoc) =
                vsep annonsDoc 
                <.> if isRef then txt "ref" else empty
                <+> txt "enum"
                <+> dpName name
                <^> ppEnumRawType rawtypeDoc
                <.> indent dpTabsize (tagsDoc |> vsep)
                <.> match membersDoc with | [] -> empty | _ -> txt "extension"
                <.> indent dpTabsize (membersDoc |> vsep)
                <.> txt "end"  
        
            let fStructTypeDecl (_, isRef, name, fieldsDoc, membersDoc, annonsDoc) =
                vsep annonsDoc 
                <.> if isRef then txt "ref" else empty
                <+> txt "struct" 
                <+> dpName name
                <.> indent dpTabsize (fieldsDoc |> vsep)
                <.> match membersDoc with | [] -> empty | _ -> txt "extension"
                <.> indent dpTabsize (membersDoc |> vsep)
                <.> txt "end"

            let fNewTypeDecl (_, isRef, name, represents, members, annons) =
                vsep annons
                <.> if isRef then txt "ref" else empty
                <+> txt "type" 
                <+> dpName name
                <+> (dpAliasedType represents
                     |> gnest dpTabsize)
                <.> match members with | [] -> empty | _ -> txt "extension"
                <.> indent dpTabsize (members |> vsep)
                <.> txt "end"

            let fTypeAliasDecl (_, name, aliasForType, annotations) =
                vsep annotations
                <.> txt "type" <+> dpName name
                <+> (chr '=' <.> aliasForType
                     |> gnest dpTabsize)

            let fClockDef _ = empty

            let rec ppAttribute attr =
                let ppKey = function
                    | Quoted (text=k) -> txt k |> dquotes
                    | Ident (text=k) -> txt k
            
                match attr with
                | Key (key, range) ->
                    ppKey key
                | KeyValue (key, value, range) ->
                    ppKey key <+>
                    (chr '=' <.> ppLiteral value |> gnest dpTabsize)
                | Structured (key, attrs, range) ->
                    ppKey key <^> 
                    (
                    (List.map (fun a -> ppAttribute a) attrs) 
                        |> dpCommaSeparatedInParens
                        |> align
                        |> group)

            let fAnnotation = function
                | Annotation (attr, _) ->
                    chr '@' <^> (ppAttribute attr |> brackets)

            let fPragma = function
                | Annotation (attr, _) ->
                    txt "@@" <^> (ppAttribute attr |> brackets)

        
            let fNameBinding (_, doc) = doc // TODO: any syntax difference between those two

            // call the catamorphism using the functions defined above
            // signature is
            // postOrderWalk            fNothing fPragma fPackage fImport fPackageMember fSubprogram fFunctionPrototype fStmt fNameBinding fAssign fAssert fAssume fAwait fITE fMatch fCobegin fWhile fRepeat fNumericFor fIteratorFor fPreempt fSubScope fActCall fFunCall fEmit fReturn fVarDecl fParamDecl fReturnDecl fUnitDecl fClockDecl fEnumTypeDecl fTagDecl fStructTypeDecl fNewTypeDecl fTypeAliasDecl fReceiver fLexpr fExpr fCondition fDataType fUnitExpr fClockDef fAnnotation treeNode : 'r=
            let doc = AST.postOrderWalk fNothing fPragma fPackage fImport fMember        fSubProgram fFunctionPrototype fStmt fNameBinding fAssign fAssert fAssume fAwait fITE fMatch fCobegin fWhile fRepeat fNumericFor fIteratorFor fPreempt fSubScope fActCall fFunCall fEmit fReturn fVarDecl fParamDecl fReturnDecl fUnitDecl fClockDecl fEnumTypeDecl fTagDecl fStructTypeDecl fNewTypeDecl fTypeAliasDecl fReceiver fLexpr fExpr fCondition fDataType fUnitExpr fClockDef fAnnotation node
            render (Some 72) doc

        // end of template