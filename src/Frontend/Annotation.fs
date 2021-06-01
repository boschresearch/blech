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

[<RequireQualifiedAccess>]
module Annotation =
    open Blech.Common
    open Attribute
    open TypeCheckContext
    open TyChecked

    let private unsupportedAnnotation (anno : AST.Annotation)  = 
        Error [UnsupportedAnnotation anno.Range ]

    let private missingAnnotation range key =
        Error [MissingAnnotation (range, key)]
        
    let private multipleUniqueAnnotation (anno : AST.Annotation)  = 
        Error [MultipleUniqueAnnotation (anno.Range, anno.Range)] //TODO: correct this

    let private missingNamedArgument range key =
        Error [MissingNamedArgument (range, key) ]

    let private bindingParameterOutOfBounds range indexes = 
        let indices = List.map (fun i -> Bindings.parameterIndexToString i) indexes
        Error [ BindingIndexOutOfBounds (range, indices)]

    /// Creates a typed annotation from an admissible untyped annotation
    // recursive decent

    let private checkDocAnnotation docAttr value = 
        match value with
        | AST.String(value = doc) -> Ok <| docAttr doc
        | _ -> Error [UnsupportedAnnotation value.Range]

    let private checkCFunctionAliasSource alias source =
        match source with
        | AST.String (value = source)
        | AST.MultiLineString (value = source) ->
            Ok <| CFunctionBinding (alias, Some source)
        | literal ->
            Error [ UnsupportedAnnotation literal.Range ]

    let private checkCFunctionBindingHeader binding header =
        match header with
        | AST.String (value = header)
        | AST.MultiLineString (value = header) ->
            Ok <| CFunctionBinding (binding, Some header)
        | literal ->
            Error [ UnsupportedAnnotation literal.Range ]

    let private checkCDataBindingHeader cdata binding header =
        match header with
        | AST.String (value = header)
        | AST.MultiLineString (value = header) ->
            Ok <| cdata (binding, Some header)
        | literal ->
            Error [ UnsupportedAnnotation literal.Range ]
    
    let private checkCFunctionSource binding optHeader =
        match optHeader with
        | [] -> 
            Ok <| CFunctionAlias (binding, None)
        | [ AST.KeyValue (key = AST.Ident(text = Key.source); value = source ) ] ->
            checkCFunctionAliasSource binding source
        | literal :: _ ->
            Error [ UnsupportedAnnotation literal.Range ]

    let private checkCFunctionHeader binding optHeader =
        match optHeader with
        | [] -> 
            Ok <| CFunctionBinding (binding, None)
        | [ AST.KeyValue (key = AST.Ident(text = Key.header); value = header ) ] ->
            checkCFunctionBindingHeader binding header
        | literal :: _ ->
            Error [ UnsupportedAnnotation literal.Range ]

    let private checkCFunctionAlias (alias : AST.Literal) optSource = 
        match alias  with
        | AST.String (value = text)
        | AST.MultiLineString (value = text) -> 
            checkCFunctionSource text optSource
        | binding -> 
            Error [UnsupportedAnnotation binding.Range]

    let private checkCDataHeader cdata binding optHeader =
        match optHeader with
        | [] -> 
            Ok <| cdata (binding, None)
        | [ AST.KeyValue (key = AST.Ident(text = Key.header); value = header ) ] ->
            checkCDataBindingHeader cdata binding header
        | literal :: _ ->
            Error [ UnsupportedAnnotation literal.Range ]

    let private checkCFunctionBinding (binding : AST.Literal) optHeader = 
        match binding  with
        | AST.String (value = text)
        | AST.MultiLineString (value = text) -> 
            checkCFunctionHeader text optHeader
        | binding -> 
            Error [UnsupportedAnnotation binding.Range]

    let private checkCDataBinding cdata (binding : AST.Literal) optHeader = 
        match binding  with
        | AST.String (value = text)
        | AST.MultiLineString (value = text) -> 
            checkCDataHeader cdata text optHeader
        | binding -> 
            Error [UnsupportedAnnotation binding.Range]

    let private checkCFunctionAnnotation (attrs : AST.Attribute list) = 
        match List.head attrs with
        |  AST.KeyValue (key = AST.Ident(text = Key.binding); value = binding) 
            -> checkCFunctionBinding binding (List.tail attrs)        
        |  AST.KeyValue (key = AST.Ident(text = Key.alias); value = alias) 
            -> checkCFunctionAlias alias (List.tail attrs)        
        |  hd -> 
            Error [ UnsupportedAnnotation hd.Range ]

    let private checkCDataAnnotation cdata (attrs : AST.Attribute list) = 
        match List.head attrs with
        |  AST.KeyValue (key = AST.Ident(text = Key.binding); value = binding) 
            -> checkCDataBinding cdata binding (List.tail attrs)        
        |  hd -> 
            Error [ UnsupportedAnnotation hd.Range ]

    let private checkKeyAnnotation (key : AST.Key) =
        match key with
        | AST.Ident(text = Attribute.entrypoint) -> Ok EntryPoint
        | AST.Ident(text = Attribute.opaqueArray) -> Ok OpaqueArray
        | AST.Ident(text = Attribute.opaqueStruct) -> Ok OpaqueStruct
        | AST.Ident(text = Attribute.simpleType)  -> Ok SimpleType
        | _ -> Error [UnsupportedAnnotation key.Range]

    let private checkKeyValueAnnotation key value =
        match key with
        | AST.Ident(text = Key.linedoc) -> checkDocAnnotation LineDoc value
        | AST.Ident(text = Key.blockdoc) -> checkDocAnnotation BlockDoc value 
        | _ -> Error [UnsupportedAnnotation key.Range]

    let private checkStructuredAnnotation key attrs = 
        match key with
        | AST.Ident(text = Attribute.cfunction) -> checkCFunctionAnnotation attrs
        | AST.Ident(text = Attribute.cconst) -> checkCDataAnnotation CConst attrs
        | AST.Ident(text = Attribute.cparam) -> checkCDataAnnotation CParam attrs
        | AST.Ident(text = Attribute.coutput) -> checkCDataAnnotation COutput attrs
        | AST.Ident(text = Attribute.cinput) -> checkCDataAnnotation CInput attrs
        // | AST.Ident(text = Attribute.ctype) -> checkCTypeAnnotation CType attrs
        | _ -> Error [UnsupportedAnnotation key.Range]

    let private checkAttribute (attr: AST.Attribute) : Result<Attribute, TyCheckError list> =
        match attr with
        | AST.Key (key = key) -> checkKeyAnnotation key
        | AST.KeyValue ( key = key;  value = value ) -> checkKeyValueAnnotation key value
        | AST.Structured ( key = key; attrs = attrs ) -> checkStructuredAnnotation key attrs

    let checkAnnotation (anno: AST.Annotation) : Result<Attribute, TyCheckError list> = 
        checkAttribute anno.Attribute
        // match anno.Attribute with
        // | AST.Key ( key = AST.Ident(text = Attribute.entrypoint) ) ->
        //     Ok EntryPoint

        // | AST.Key ( key = AST.Ident(text = Attribute.opaqueArray) ) ->
        //     Ok OpaqueArray
        
        // | AST.Key ( key = AST.Ident(text = Attribute.opaqueStruct) ) ->
        //     Ok OpaqueStruct
        
        // | AST.Key ( key = AST.Ident(text = Attribute.simpleType) ) ->
        //     Ok SimpleType

        // | AST.KeyValue ( key = AST.Ident(text = Key.linedoc) 
        //                  value = AST.String(value = doc) ) ->
        //     Ok (LineDoc (doc))

        // | AST.KeyValue ( key = AST.Ident(text = Key.blockdoc) 
        //                  value = AST.String(value = doc) ) ->
        //     Ok (BlockDoc (doc))
               
        // | AST.Structured( key = AST.Ident(text = Attribute.cfunction) 
        //                   attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
        //                                           value = binding)
        //                             AST.KeyValue (key = AST.Ident(text = Key.header) 
        //                                           value = header) ] ) 
        //                                                 when binding.IsText && header.IsText ->
        //     Ok (CFunctionBinding(binding.Text, Some header.Text))

        // | AST.Structured( key = AST.Ident(text = Attribute.cfunction) 
        //                   attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
        //                                           value = binding) ] ) 
        //                                                 when binding.IsText ->
        //     Ok (CFunctionBinding(binding.Text, None))

        // | AST.Structured( key = AST.Ident(text = Attribute.cfunction) 
        //                   attrs = [ AST.KeyValue (key = AST.Ident(text = Key.source)) ] ) ->
        //     //Ok (CFunctionWrapper source)
        //     Error [DeprecatedCFunctionWrapper anno.Range ]

        // | AST.Structured( key = AST.Ident(text = Attribute.cconst) 
        //                   attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
        //                                           value = binding)
        //                             AST.KeyValue (key = AST.Ident(text = Key.header) 
        //                                           value = header) ] ) 
        //                                                when binding.IsText && header.IsText ->
        //     Ok (CConst(binding.Text, Some header.Text))
        
        // | AST.Structured( key = AST.Ident(text = Attribute.cconst) 
        //                   attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
        //                                           value = binding) ] ) 
        //                                                 when binding.IsText->
        //     Ok (CConst(binding.Text, None))

        // | AST.Structured( key = AST.Ident(text = Attribute.cinput) 
        //                   attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
        //                                           value = binding)
        //                             AST.KeyValue (key = AST.Ident(text = Key.header) 
        //                                           value = header) ] ) 
        //                                                 when binding.IsText && header.IsText ->
        //     Ok (CInput(binding.Text, Some header.Text))

        // | AST.Structured( key = AST.Ident(text = Attribute.cinput) 
        //                   attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
        //                                           value = binding) ] ) 
        //                                                 when binding.IsText ->
        //     Ok (CInput(binding.Text, None))

        // | AST.Structured( key = AST.Ident(text = Attribute.coutput) 
        //                   attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
        //                                           value = binding)
        //                             AST.KeyValue (key = AST.Ident(text = Key.header) 
        //                                           value = header) ] ) 
        //                                             when binding.IsText && header.IsText ->
        //     Ok (COutput(binding.Text, Some header.Text))
        
        // | AST.Structured( key = AST.Ident(text = Attribute.coutput) 
        //                   attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
        //                                           value = AST.String(value = binding)) ] ) ->
        //     Ok (COutput(binding, None))
                
        // | _ ->
        //     Error [UnsupportedAnnotation anno.Range]

    
    let checkSubProgram (sp: AST.SubProgram) =
        let checkSpAnno spattr anno = 
            let checkAttribute (spattr, attr) = 
                match attr with
                | EntryPoint when not sp.isFunction -> 
                    if Option.isSome spattr.entryPoint then
                        multipleUniqueAnnotation anno 
                    else
                        Ok { spattr with entryPoint = Some attr }
                | LineDoc _
                | BlockDoc _ ->
                    Ok { spattr with doc = List.append spattr.doc [attr] }        
                | _ ->
                    unsupportedAnnotation anno

            combine spattr (checkAnnotation anno)
            |> Result.bind checkAttribute
        List.fold checkSpAnno (Ok Attribute.SubProgram.Empty) sp.annotations
     
     
    let checkFunctionPrototype (lut: TypeCheckContext) (fp: AST.Prototype) =
        let checkFpAnno fpattr anno = 
            let checkAttribute (fpattr, attr) = 
                match attr with
                | CFunctionBinding (header = header) when fp.isExtern && fp.isFunction ->
                    if Option.isSome fpattr.cfunction then
                        multipleUniqueAnnotation anno
                    elif Option.isNone header && not (hasInclude lut) then 
                        missingNamedArgument fp.range Attribute.Key.header
                    else
                        Ok { fpattr with cfunction = Some attr }
                | CFunctionAlias _ when fp.isExtern && fp.isFunction ->
                    if Option.isSome fpattr.cfunction then
                        multipleUniqueAnnotation anno
                    else
                        Ok { fpattr with cfunction = Some attr }
                | LineDoc _
                | BlockDoc _ ->
                    Ok { fpattr with doc = List.append fpattr.doc [attr] }        
                | _ ->
                    unsupportedAnnotation anno
        
            combine fpattr (checkAnnotation anno)
            |> Result.bind checkAttribute
        
        let checkCFunction fpattr =
            match fpattr.cfunction with
            | None when fp.isExtern && not (hasCompile lut)  ->
                missingAnnotation fp.range Attribute.cfunction
                //missingNamedArgument fp.range Attribute.Key.source
            | _ ->
                Ok fpattr
        
        let checkParameterIndex (fpattr : FunctionPrototype)  =
            match fpattr.TryGetCBinding with
            | Some cbinding ->
                let returnIdx = // if extern function returns a complex value, 
                                // we assume there is an extra parameter for this in the C function
                    match fp.result with 
                    | None -> 0
                    | Some r -> if r.datatype.IsSimple then 0 else 1
                let maxIndex = List.length fp.inputs + List.length fp.outputs + returnIdx
                let idcsOutOfBounds = List.filter (fun i -> i < 1 || i > maxIndex) (Bindings.getParameterIndices cbinding)
                if List.isEmpty idcsOutOfBounds then
                    Ok fpattr
                else
                    bindingParameterOutOfBounds fp.range idcsOutOfBounds
            | None ->
                Ok fpattr
            

        List.fold checkFpAnno (Ok Attribute.FunctionPrototype.Empty) fp.annotations
        |> Result.bind checkCFunction
        |> Result.bind checkParameterIndex 

    
    let checkOpaqueSingleton (lut: TypeCheckContext) (os: AST.OpaqueSingleton) =
        let checkOsAnno osattr anno = 
            let checkAttribute (fpattr, attr) = 
                match attr with
                | CFunctionBinding (header = header) ->
                    if Option.isSome fpattr.cfunction then
                        multipleUniqueAnnotation anno
                    elif Option.isNone header && not (hasInclude lut) then 
                        missingNamedArgument os.range Attribute.Key.header
                    else
                        Ok { fpattr with cfunction = Some attr }
                | CFunctionAlias _ ->
                    if Option.isSome fpattr.cfunction then
                        multipleUniqueAnnotation anno
                    else
                        Ok { fpattr with cfunction = Some attr }
                | LineDoc _
                | BlockDoc _ ->
                    Ok { fpattr with doc = List.append fpattr.doc [attr] }        
                | _ ->
                    unsupportedAnnotation anno
        
            combine osattr (checkAnnotation anno)
            |> Result.bind checkAttribute
        
        List.fold checkOsAnno (Ok Attribute.FunctionPrototype.Empty) os.annotations
        

    let checkVarDecl lut (v: AST.VarDecl) =
        let checkVdAnnotation vdattr (anno: AST.Annotation) =
            let checkAttribute (vdattr, attr) =
                match attr with
                | CConst (header = header) when v.isExtern && v.permission.IsConst ->
                    if Option.isSome vdattr.cvardecl then
                        multipleUniqueAnnotation anno
                    elif Option.isNone header && not (hasInclude lut) then 
                        missingNamedArgument v.range Attribute.Key.header
                    else
                        Ok { vdattr with cvardecl = Some attr }
                | CInput (header = header) when v.isExtern && v.permission.IsLet ->
                    if Option.isSome vdattr.cvardecl then
                        multipleUniqueAnnotation anno
                    elif Option.isNone header && not (hasInclude lut) then 
                        missingNamedArgument v.range Attribute.Key.header
                    else
                        Ok { vdattr with cvardecl = Some attr }
                | COutput (header = header) when v.isExtern && v.permission.IsVar ->
                    if Option.isSome vdattr.cvardecl then
                        multipleUniqueAnnotation anno
                    elif Option.isNone header && not (hasInclude lut) then 
                        missingNamedArgument v.range Attribute.Key.header
                    else
                        Ok { vdattr with cvardecl = Some attr }
                | LineDoc _
                | BlockDoc _ ->
                    Ok { vdattr with doc = List.append vdattr.doc [attr] }        
                | _ ->
                    unsupportedAnnotation anno

            combine vdattr (checkAnnotation anno)
            |> Result.bind checkAttribute

        let checkExternVarDecl vdattr =
            match vdattr.cvardecl with
            | None when v.isExtern && v.permission.IsConst ->
                missingAnnotation v.range Attribute.cconst
            | None when v.isExtern && v.permission.IsLet ->
                missingAnnotation v.range Attribute.cinput
            | None when v.isExtern && v.permission.IsVar ->
                missingAnnotation v.range Attribute.coutput
            | _ ->
                Ok vdattr
    
        List.fold checkVdAnnotation (Ok VarDecl.Empty) v.annotations
        |> Result.bind checkExternVarDecl


    let checkOtherDecl (annotations: AST.Annotation list) =  
        let checkOdAnnotation odattr (anno: AST.Annotation) = 
            let checkAttribute (odattr, attr) =
                match attr with
                | LineDoc _
                | BlockDoc _ 
                // TODO: Wrong usage, should have a separate annotation check, correct this. fjg. 23.05.21
                | SimpleType 
                | OpaqueStruct
                | OpaqueArray ->
                    Ok { odattr with OtherDecl.doc = List.append odattr.doc [attr] }
                | _ ->
                    unsupportedAnnotation anno

            combine odattr (checkAnnotation anno)
            |> Result.bind checkAttribute
         
        List.fold checkOdAnnotation (Ok Attribute.OtherDecl.Empty) annotations   

    
    let checkModuleSpec (modSpec : AST.ModuleSpec) =
        let checkMsAnnotation msattr (anno : AST.Annotation) =
            let checkAttribute (msattr, attr) =
                match attr with
                | LineDoc _
                | BlockDoc _ ->
                    Ok { msattr with OtherDecl.doc = List.append msattr.doc [attr] }
                | _ ->
                    unsupportedAnnotation anno

            combine msattr (checkAnnotation anno)
            |> Result.bind checkAttribute
        List.fold checkMsAnnotation (Ok Attribute.OtherDecl.Empty) modSpec.annotations   
   

    //--------------
    //--- Pragmas
    //--------------

    let private unknownPragma (anno : AST.Annotation)  = 
        Error [UnknownPragma anno.Range ]

    let private checkPragma (pragma: AST.Annotation) =
        match pragma.Attribute with       
        | AST.Structured( key = AST.Ident(text = Attribute.cinclude) 
                          attrs = [ AST.KeyValue (key = AST.Ident(text = Key.header) 
                                                  value = AST.String(value = header)) ] ) ->
            Ok (CInclude header)
            
        | AST.Structured( key = AST.Ident(text = Attribute.ccompile) 
                          attrs = [ AST.KeyValue (key = AST.Ident(text = Key.source) 
                                                  value = AST.String(value = source)) ] ) ->
            Ok (CCompile source)
            
        | _ ->
            unknownPragma pragma
      

    let checkMemberPragma lut (pragma: AST.Annotation) = 
        let checkDirective directive =
            match directive with
            | CInclude _
            | CCompile _ ->
                do addPragmaToLut lut directive
                Ok directive
            
        checkPragma pragma 
        |> Result.bind checkDirective 

