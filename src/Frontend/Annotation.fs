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
    open Attribute
    open TypeCheckContext
    open TyChecked
    
    let private unknownAnnotation (anno : AST.Annotation)  = 
        Error [UnknownAnnotation anno.Range ]

    let private missingAnnotation range key =
        Error [MissingAnnotation (range, key)]
        
    let private multipleUniqueAnnotation (anno : AST.Annotation)  = 
        Error [MultipleUniqueAnnotation (anno.Range, anno.Range)] //TODO: correct this

    let private missingNamedArgument range key =
        Error [MissingNamedArgument (range, key) ]

    /// Creates a typed annotation from an admissible untyped annotation
    // recursive decent is currently not neccessary
    let checkAnnotation (anno: AST.Annotation) : Result<Attribute, TyCheckError list> = 
        match anno.Attribute with
        | AST.Key ( key = AST.Ident(text = Attribute.entrypoint) ) ->
            Ok EntryPoint
        
        | AST.KeyValue ( key = AST.Ident(text = Key.linedoc) 
                         value = AST.String(value = doc) ) ->
            Ok (LineDoc (doc))

        | AST.KeyValue ( key = AST.Ident(text = Key.blockdoc) 
                         value = AST.String(value = doc) ) ->
            Ok (BlockDoc (doc))
               
        | AST.Structured( key = AST.Ident(text = Attribute.cfunction) 
                          attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
                                                  value = AST.String(value = binding))
                                    AST.KeyValue (key = AST.Ident(text = Key.header) 
                                                  value = AST.String(value = header)) ] ) ->
            Ok (CFunctionPrototype(binding, Some header))

        | AST.Structured( key = AST.Ident(text = Attribute.cfunction) 
                          attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
                                                  value = AST.String(value = binding)) ] ) ->
            Ok (CFunctionPrototype(binding, None))

        | AST.Structured( key = AST.Ident(text = Attribute.cfunction) 
                          attrs = [ AST.KeyValue (key = AST.Ident(text = Key.source) 
                                                  value = AST.String(value = source)) ] ) ->
            Ok (CFunctionWrapper source)

        | AST.Structured( key = AST.Ident(text = Attribute.cconst) 
                          attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
                                                  value = AST.String(value = binding))
                                    AST.KeyValue (key = AST.Ident(text = Key.header) 
                                                  value = AST.String(value = header)) ] ) ->
            Ok (CConst(binding, Some header))
        
        | AST.Structured( key = AST.Ident(text = Attribute.cconst) 
                          attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
                                                  value = AST.String(value = binding)) ] ) ->
            Ok (CConst(binding, None))
                
        | _ ->
            Error [UnknownAnnotation anno.Range]

    
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
                    unknownAnnotation anno

            combine spattr (checkAnnotation anno)
            |> Result.bind checkAttribute
        List.fold checkSpAnno (Ok Attribute.SubProgram.Empty) sp.annotations
     
     
    let checkFunctionPrototype (lut: TypeCheckContext) (fp: AST.Prototype) =
        let checkFpAnno fpattr anno = 
            let checkAttribute (fpattr, attr) = 
                match attr with
                | CFunctionPrototype (header = header) when fp.isExtern && fp.isFunction ->
                    if Option.isSome fpattr.cfunction then
                        multipleUniqueAnnotation anno
                    elif Option.isNone header && not (hasInclude lut) then 
                        missingNamedArgument fp.range Attribute.Key.header
                    else
                        Ok { fpattr with cfunction = Some attr }
                | CFunctionWrapper _ when fp.isExtern && fp.isFunction ->
                    if Option.isSome fpattr.cfunction then
                        multipleUniqueAnnotation anno
                    else
                        Ok { fpattr with cfunction = Some attr }
                | LineDoc _
                | BlockDoc _ ->
                    Ok { fpattr with doc = List.append fpattr.doc [attr] }        
                | _ ->
                    unknownAnnotation anno
        
            combine fpattr (checkAnnotation anno)
            |> Result.bind checkAttribute
        
        let checkCFunction fpattr =
            match fpattr.cfunction with
            | None when fp.isExtern && not (hasCompile lut)  ->
                missingNamedArgument fp.range Attribute.Key.source
            | _ ->
                Ok fpattr
        
        List.fold checkFpAnno (Ok Attribute.FunctionPrototype.Empty) fp.annotations
        |> Result.bind checkCFunction

    
    let checkVarDecl lut (v: AST.VarDecl) =
        let checkVdAnnotation vdattr (anno: AST.Annotation) =
            let checkAttribute (vdattr, attr) =
                match attr with
                | CConst (header = header)  when v.isExtern && v.permission.IsConst ->
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
                    unknownAnnotation anno

            combine vdattr (checkAnnotation anno)
            |> Result.bind checkAttribute

        let checkCVarDecl vdattr =
            match vdattr.cvardecl with
            | None when v.isExtern && v.permission.IsConst ->
                missingAnnotation v.range Attribute.cconst
            | _ ->
                Ok vdattr
    
        List.fold checkVdAnnotation (Ok VarDecl.Empty) v.annotations
        |> Result.bind checkCVarDecl


    let checkOtherDecl (annotations: AST.Annotation list) =  
        let checkOdAnnotation odattr (anno: AST.Annotation) = 
            let checkAttribute (odattr, attr) =
                match attr with
                | LineDoc _
                | BlockDoc _ ->
                    Ok { odattr with OtherDecl.doc = List.append odattr.doc [attr] }        
                | _ ->
                    unknownAnnotation anno

            combine odattr (checkAnnotation anno)
            |> Result.bind checkAttribute
         
        List.fold checkOdAnnotation (Ok Attribute.OtherDecl.Empty) annotations   

    
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

