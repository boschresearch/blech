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

module Attribute =
    
    open Blech.Common.PPrint
    open DocPrint
    
    // sub programs
    [<Literal>] 
    let entrypoint = "EntryPoint"

    // function prototypes
    [<Literal>] 
    let cfunction = "CFunction"
    
    // var decls
    [<Literal>] 
    let cconst = "CConst"
    [<Literal>] 
    let cparam = "CParam"
    [<Literal>] 
    let coutput = "COutput"
    [<Literal>] 
    let cinput = "CInput"

    // type decls
    [<Literal>] 
    let ctype = "CType"
    
    // c pragmas
    [<Literal>]
    let cinclude = "CInclude"
    [<Literal>]
    let ccompile = "CCompile"

    // opaque types qualification
    [<Literal>] 
    let opaqueStruct = "StructType"
    [<Literal>] 
    let opaqueArray = "ArrayType"
    [<Literal>] 
    let simpleType = "SimpleType"

    module Key =

        // C bindings
        [<Literal>] 
        let binding = "binding"
        [<Literal>] 
        let header = "header"
        [<Literal>] 
        let source = "source"

        // C alias 
        [<Literal>] 
        let alias = "alias"
        
        // C typedef
        [<Literal>] 
        let typedef = "typedef"

        // doc comments
        [<Literal>] 
        let linedoc = "linedoc"
        [<Literal>] 
        let blockdoc = "blockdoc"

    
    type Attribute =
        // declaration attributes
        | EntryPoint

        | CConst of binding: string * header: string option
        | CParam of binding: string * header: string option
        | COutput of binding: string * header: string option
        | CInput of binding: string * header: string option

        | CFunctionBinding of binding: string * header: string option
        | CFunctionAlias of alias: string * source: string option
        
        | LineDoc of linedoc: string
        | BlockDoc of blockdoc: string

        | CType of typedef: string

        | OpaqueArray
        | OpaqueStruct
        | SimpleType
    
        member attr.ToDoc =
            let dpStructured key attrs =
                key <+> dpCommaSeparatedInParens attrs
            
            let dpKeyValue key value = 
                key <+> chr '=' <+> value
            
            let dpAnno attr = 
                chr '@' <^> brackets attr
            
            let dpCBinding key cbinding optCheader =
                let attrs = 
                    match optCheader with   
                    | Some cheader ->
                        [ dpKeyValue (txt Key.binding) cbinding 
                          dpKeyValue (txt Key.header) (dquotes cheader) ]
                    | None ->
                        [ dpKeyValue (txt Key.binding) cbinding ]
                        
                dpStructured key attrs
                |> dpAnno

            let dpCAlias key cAlias optCSource =
                dpCBinding key cAlias optCSource

            let dpCType key typedef =
                dpStructured key [dpKeyValue (txt Key.typedef) typedef]

            let optStringToDoc optString = 
                match optString with
                | Some s -> Some <| txt s
                | None -> None

            match attr with
            | EntryPoint ->
                txt entrypoint |> dpAnno
            
            | CConst (binding, header)->
                dpCBinding (txt cconst) (txt binding) (optStringToDoc header)
            | CParam (binding, header)->
                dpCBinding (txt cparam) (txt binding) (optStringToDoc header)
            | COutput (binding, header)->
                dpCBinding (txt coutput) (txt binding) (optStringToDoc header)
            | CInput (binding, header)->
                dpCBinding (txt cinput) (txt binding) (optStringToDoc header)
            
            | CFunctionBinding (binding, header) ->
                dpCBinding (txt cfunction) (txt binding) (optStringToDoc header)
            | CFunctionAlias (alias, source) ->  
                dpCAlias (txt cfunction) (txt alias) (optStringToDoc source)
            
            | LineDoc doc ->
                txt "///" <+> txt doc
            | BlockDoc doc ->
                txt "/**" <^> txt doc <^> txt "*/"

            | CType typedef ->
                dpCType (txt ctype) (txt typedef)

            | OpaqueStruct ->
                txt opaqueStruct |> dpAnno
            | OpaqueArray ->
                txt opaqueArray |> dpAnno
            | SimpleType ->
                txt simpleType |> dpAnno


        override attr.ToString() =
            render None <| attr.ToDoc


    //--- 
    //  Helper functions for printing declaration attributes 
    // ---

    let private dpAttrList attrs = 
        List.map (fun (attr: Attribute) -> attr.ToDoc) attrs
        
 
    let private declToDoc (docs: Attribute list) (optAttr: Attribute option) =
        match optAttr with
        | Some attr ->
            dpAttrList docs @ [attr.ToDoc]
        | None ->
            dpAttrList docs

    let private dpStructured key attrs =
        key <+> dpCommaSeparatedInParens attrs
            
    let private dpKeyValue key value = 
        key <+> chr '=' <+> value

    //---
    // Helper function for accessing c bindings
    //---

    let private tryGetCBinding (attr: Attribute) =
        match attr with
        | CConst (binding = binding)
        | CParam (binding = binding)
        | COutput (binding = binding)
        | CInput (binding = binding)
        | CFunctionBinding (binding = binding) ->
            Some binding
        | _ ->
            None

    let private tryGetCHeader (attr: Attribute) =
        match attr with
        | CConst (header = Some header)
        | CParam (header = Some header)
        | COutput (header = Some header)
        | CInput (header = Some header)
        | CFunctionBinding (header = Some header) ->
            Some header
        | _ ->
            None

    let private tryGetCAlias (attr: Attribute) =
        match attr with
        | CFunctionAlias (alias = alias) -> 
            Some alias
        | _ ->
            None

    let private tryGetCSource (attr: Attribute) =
        match attr with
        | CFunctionAlias (source = source) -> 
            Some source
        | _ ->
            None

    let private tryGetCTypedef (attr: Attribute) =
        match attr with
        | CType (typedef = typedef) ->
            Some typedef
        | _ ->
            None        


    //---
    // Declaration attributes
    // ---

    /// Attributes for typed subprograms
    type SubProgram = 
        {
            doc: Attribute list
            entryPoint: Attribute option
        }
        static member Empty = 
            { doc = []
              entryPoint = None }

        member this.ToDoc = 
            declToDoc this.doc this.entryPoint
            
        override this.ToString() =
            this.ToDoc
            |> vsep
            |> render None


     /// Attributes for typed function prototypes   
     type FunctionPrototype = 
        {
            doc: Attribute list
            cfunction: Attribute option
        }
        static member Empty = 
            { doc = []
              cfunction = None }

        member this.ToDoc = 
            declToDoc this.doc this.cfunction

        override this.ToString() =
            this.ToDoc
            |> vsep
            |> render None

        member fpanno.isDirectCCall =
            match fpanno.cfunction with
            | Some (CFunctionBinding (binding = _)) ->
                true
            | _ ->
                false

        member fpanno.TryGetCHeader =
            match fpanno.cfunction with
            | Some cattr ->
                tryGetCHeader cattr
            | _ ->
                None
        
        member fpanno.TryGetCBinding = 
            match fpanno.cfunction with
            | Some cattr ->
                tryGetCBinding cattr
            | _ ->
                None

    /// Attribute for typed variable declarations
    type VarDecl = 
        {
            doc: Attribute list
            cvardecl: Attribute option
        }
        static member Empty = 
            { doc = []
              cvardecl = None }

        member this.ToDoc = 
            declToDoc this.doc this.cvardecl

        override this.ToString() =
            this.ToDoc
            |> vsep
            |> render None

        member this.TryGetCHeader =
            match this.cvardecl with
            | Some cattr  ->
                tryGetCHeader cattr
            | _ ->
                None

        member fpanno.TryGetCBinding = 
            match fpanno.cvardecl with
            | Some cattr ->
                tryGetCBinding cattr
            | _ ->
                None

                
    type OpaqueTypeDecl = 
        { 
            doc: Attribute list
            opaquekind: Attribute option // StructType, ArrayType, SimpleType
        }
        static member Empty = 
            { doc = []
              opaquekind = None }
        
        member this.ToDoc = 
            declToDoc this.doc this.opaquekind

        override this.ToString() =
            this.ToDoc 
            |> vsep
            |> render None

    /// Used as a general purpose type for any other annotateable declaration
    type OtherDecl = 
        { 
            doc: Attribute list
        }
        static member Empty = 
            { doc = [] }
        
        member this.ToDoc = 
            declToDoc this.doc None

        override this.ToString() =
            this.ToDoc 
            |> vsep
            |> render None


    //---
    // Member level attributes - pragmas
    // ---
    
    type MemberPragma = 
        | CInclude of header: string
        | CCompile of source: string

        member attr.ToDoc =
            let dpPragma attr =
                txt "@@" <^> brackets attr

            let dpCInclude cheader =
                ( dpStructured 
                  <| txt cinclude
                  <| [ dpKeyValue (txt Key.header) (dquotes <| cheader) ] )                
                |> dpPragma

            let dpCCompile csource =
                ( dpStructured 
                  <| txt ccompile
                  <| [ dpKeyValue (txt Key.source) (dquotes <| csource) ] )                
                |> dpPragma

            match attr with
            | CInclude header ->
                dpCInclude (txt header)
            | CCompile source ->
                dpCCompile (txt source)
                
        override attr.ToString() =
            render None <| attr.ToDoc

        member this.IsInclude =
            match this with
            | CInclude _ -> true
            | _ -> false
        
        member this.IsCompile =
            match this with
            | CCompile _ -> true
            | _ -> false

        member this.TryGetCHeader = 
            match this with
            | CInclude header ->
                Some header
            | _ ->
                None