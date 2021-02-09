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
    // recursive decent is currently not neccessary
    let checkAnnotation (anno: AST.Annotation) : Result<Attribute, TyCheckError list> = 
        match anno.Attribute with
        | AST.Key ( key = AST.Ident(text = Attribute.entrypoint) ) ->
            Ok EntryPoint

        | AST.Key ( key = AST.Ident(text = Attribute.complexType) ) ->
            Ok ComplexType
        
        | AST.Key ( key = AST.Ident(text = Attribute.simpleType) ) ->
            Ok SimpleType

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
                          attrs = [ AST.KeyValue (key = AST.Ident(text = Key.source)) ] ) ->
            //Ok (CFunctionWrapper source)
            Error [DeprecatedCFunctionWrapper anno.Range ]

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

        | AST.Structured( key = AST.Ident(text = Attribute.cinput) 
                          attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
                                                  value = AST.String(value = binding))
                                    AST.KeyValue (key = AST.Ident(text = Key.header) 
                                                  value = AST.String(value = header)) ] ) ->
            Ok (CInput(binding, Some header))

        | AST.Structured( key = AST.Ident(text = Attribute.cinput) 
                          attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
                                                  value = AST.String(value = binding)) ] ) ->
            Ok (CInput(binding, None))

        | AST.Structured( key = AST.Ident(text = Attribute.coutput) 
                          attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
                                                  value = AST.String(value = binding))
                                    AST.KeyValue (key = AST.Ident(text = Key.header) 
                                                  value = AST.String(value = header)) ] ) ->
            Ok (COutput(binding, Some header))
        
        | AST.Structured( key = AST.Ident(text = Attribute.coutput) 
                          attrs = [ AST.KeyValue (key = AST.Ident(text = Key.binding) 
                                                  value = AST.String(value = binding)) ] ) ->
            Ok (COutput(binding, None))
                
        | _ ->
            Error [UnsupportedAnnotation anno.Range]

    
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
                | CFunctionPrototype (header = header) ->
                    if Option.isSome fpattr.cfunction then
                        multipleUniqueAnnotation anno
                    elif Option.isNone header && not (hasInclude lut) then 
                        missingNamedArgument os.range Attribute.Key.header
                    else
                        Ok { fpattr with cfunction = Some attr }
                | CFunctionWrapper _ ->
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
                | SimpleType 
                | ComplexType ->
                    Ok { odattr with OtherDecl.doc = List.append odattr.doc [attr] }
                | _ ->
                    unsupportedAnnotation anno

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

