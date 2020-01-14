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

module Blech.Backend.CodeGeneration

open Blech.Common

open Blech.Common.PPrint.PPrint

open Blech.Frontend
open Blech.Frontend.CommonTypes
open Blech.Frontend.BlechTypes
open Blech.Frontend.PrettyPrint.DocPrint

open CPdataAccess
open CPrinter


module Comment =

    let generatedCode =
        cpGeneratedComment <| txt "This is generated code - do not touch!"

    // c file comments
    
    let cheaders =
        cpGeneratedComment <| txt "used C headers"
    
    let blechHeader = 
        cpGeneratedComment <| txt "blech types"
    
    let selfInclude = 
        cpGeneratedComment <| txt "exports, user types and C wrappers"

    let cConstants = 
        cpGeneratedComment <| txt "direct C constants"
    
    let cFunctions = 
        cpGeneratedComment <| txt "direct C functions"
    
    //let constants = 
    //    cpGeneratedComment <| txt "constants"

    let parameters = 
        cpGeneratedComment <| txt "parameters"
    
    let state = 
        cpGeneratedComment <| txt "state"
    
    let compilations =  
        cpGeneratedComment <| txt "activities and functions"
    
    let progam = 
        cpGeneratedComment <| txt "blech program"
    
    // h file comments
  
    let cPrototypes = 
        cpGeneratedComment <| txt "extern functions to be implemented in C"
    
    let userTypes = 
        cpGeneratedComment <| txt "all user defined types"

    let cProgramFunctions =
        cpGeneratedComment <| txt "program functions: tick, init, printState"

    // app file comments

    let blechCInclude = 
        cpGeneratedComment <| txt "the generated blech program"
    
    let externalState =
        cpGeneratedComment <| txt "external state for the blech program"

    let testFunction = 
        cpGeneratedComment <| txt "the test main loop"


module AppName =

    let private programName id moduleName =
        QName.CreateProgramName moduleName id

    let tick = programName "tick"
    let init = programName "init"
    let printState = programName "printState"
    
    
       
/// Translates all sub programs of a module into a list of compilations
let public translate ctx (pack: BlechModule) =
    // translate all subprograms in order
    pack.funacts
    |> List.fold (fun compilations funact ->
        if funact.isFunction then FunctionTranslator.translate ctx funact
        else ActivityTranslator.translate ctx compilations funact
        |> List.singleton
        |> List.append compilations) []


/// Emit C code for module as Doc
let private cpModuleCode ctx (moduleName: SearchPath.ModuleName) 
                             (pragmas: Attribute.MemberPragma list) 
                             (compilations: Compilation list) 
                             entryPoint =
    // C header
    let programHeader = txt """#include <stdio.h>
#include <string.h>"""

    let blechHeader = txt "#include \"blech.h\""

    let inclSelfHeader =
        let hFile = txt <| SearchPath.moduleToInclude moduleName
        txt "#include" <+> dquotes hFile 

    // Blech const become #define macros in C
    // right now all go to the module code, because nothing gets exported
    // constants local to subprograms should also work

    let varDecls = 
        ctx.tcc.nameToDecl.Values
        |> Seq.choose (fun d -> match d with | Declarable.VarDecl f -> Some f | _ -> None)

    let externConsts = 
        ctx.tcc.nameToDecl.Values
        |> Seq.choose (fun d -> match d with | Declarable.ExternalVarDecl f -> Some f | _ -> None)
    
    let externConstMacros = 
        let renderExternConst (ec: ExternalVarDecl) = 
            let cexpr = 
                match ec.annotation.cvardecl with
                | Some (Attribute.CConst (binding = text)) ->
                    txt text |> parens
                | _ -> 
                    failwith "This should never happen"            
            
            let macro = 
                txt "#define" <+> ppStaticName ec.name <+> cexpr
                |> groupWith (txt " \\")
            
            cpOptDocComments ec.annotation.doc
            |> dpOptLinePrefix
            <| macro

        externConsts
        |> Seq.map renderExternConst
        |> dpBlock

    let userParams =
        let renderParam (v: VarDecl) =
            let prereqStmt, processedRhs = cpExprInFunction ctx v.initValue
            assert (List.length prereqStmt = 0)
            let decl = txt "static" <+> cpArrayDeclInActivity v.name v.datatype <+> txt "=" <+> processedRhs <^> semi

            cpOptDocComments v.annotation.doc
            |> dpOptLinePrefix
            <| decl

        varDecls
        |> Seq.filter (fun vd -> vd.mutability.Equals Mutability.StaticParameter)
        |> Seq.map renderParam
        |> dpBlock


    // Type Declarations 

    // All user types go to the header file, fjg 21.01.19
    // let userTypes = 
    //    ctx.tcc.userTypes.Values
    //    |> Seq.map (cpUserType)
    //    |> ppBlock

    // Global variables
    let entryCompilation = compilations |> List.find (fun c -> c.name = entryPoint)
    let globVars = cpMainStateAsStatics entryCompilation.iface
    
    // Translate function prototypes to direct C calls
    let functionPrototypes = 
        ctx.tcc.nameToDecl.Values
        |> Seq.choose (fun d -> match d with | Declarable.FunctionPrototype f -> Some f | _ -> None)
    
    let cCalls =
        Seq.filter (fun (fp: FunctionPrototype) -> fp.isDirectCCall) functionPrototypes

    let cHeaders = 
        let hfiles =
            let cCalls = Seq.choose (fun (fp: FunctionPrototype) -> fp.annotation.TryGetCHeader) cCalls
            let extConsts = Seq.choose (fun (vd: ExternalVarDecl) -> vd.annotation.TryGetCHeader) externConsts
            let cIncludes = List.choose (fun (mp: Attribute.MemberPragma) -> mp.TryGetCHeader) pragmas

            Seq.append extConsts cCalls 
            |> Seq.append cIncludes 
            |> Seq.distinct
        
        let includeHfile hfile = 
            txt "#include" <+> (txt hfile |> dquotes)
        
        Seq.map includeHfile hfiles
        |> dpBlock
    
    let directCCalls = 
        cCalls
        |> Seq.map (fun fp -> cpDirectCCall fp)
        |> dpToplevel


    // Translated subprograms
    let code = 
        compilations 
        |> List.map (fun c -> dpOptLinePrefix c.doc c.implementation) 
        |> dpToplevel

        

    // tick function
    let mainCallback = 
        let entryIface = 
            if true then entryCompilation.iface
            else entryCompilation.iface
        ProgramGenerator.mainCallback ctx.cliContext.passPrimitiveByAddress 
                                      (AppName.tick moduleName) 
                                      entryCompilation.name 
                                      entryIface
    
    // init function
    let mainInit = 
        ProgramGenerator.mainInit ctx (AppName.init moduleName) compilations entryCompilation
        
 
    let printState =
        ProgramGenerator.printState ctx (AppName.printState moduleName) entryCompilation
    
    // combine all into one Doc
    [ Comment.generatedCode
      programHeader
      Comment.cheaders
      cHeaders
      Comment.blechHeader
      blechHeader
      Comment.selfInclude
      inclSelfHeader
      Comment.cConstants
      externConstMacros
      Comment.cFunctions
      directCCalls
      //Comment.constants
      //userConst
      Comment.parameters
      userParams
      Comment.state
      globVars
      Comment.compilations
      code
      Comment.progam
      mainCallback
      mainInit
      printState ]
    |> dpToplevel

// end of cpModuleCode

/// Emit C header for module as Doc
let private cpModuleHeader ctx (moduleName: SearchPath.ModuleName) (compilations: Compilation list) entryPoint =
    // C header
    let guard = txt <| SearchPath.moduleToIncludeGuard moduleName
        
    let includeGuardBegin = 
        txt "#ifndef" <+> guard
        <.> txt "#define" <+> guard

    let includeGuardEnd = 
        txt "#endif" <+> enclose (txt "/* ", txt " */") guard

    let blechHeader = 
        txt "#include \"blech.h\""

    // Translate function prototypes to extern functions and direct C calls
    let functionPrototypes = 
        ctx.tcc.nameToDecl.Values
        |> Seq.choose (fun d -> match d with | Declarable.FunctionPrototype f -> Some f | _ -> None)
    
    let cCalls =
        Seq.filter (fun (fp: FunctionPrototype) -> fp.isDirectCCall) functionPrototypes

    let cWrappers = 
        Seq.except cCalls functionPrototypes

    let cCallHeaders = 
        let hfiles =
            Seq.choose(fun fp -> fp.annotation.TryGetCHeader) cCalls
            |> Seq.distinct
        
        let includeHfile hfile = 
            txt "#include" <+> (txt hfile |> dquotes)
        
        Seq.map includeHfile hfiles
        |> dpBlock
       

    // Type Declarations
    let userTypes = 
        ctx.tcc.userTypes.Values
        |> Seq.map cpUserType
        |> dpBlock


    let externFunctions =
        let ifaceOf (fp: FunctionPrototype) =
            {Iface.Empty with inputs = fp.inputs; outputs = fp.outputs}
        cWrappers
        |> Seq.map (fun fp -> cpExternFunction fp.annotation.doc fp.name (ifaceOf fp) (fp.returns) )
        |> dpToplevel

    let directCCalls = // TODO: directCCalls must not be exported, check this, fjg. 20.02.19
        cCalls
        |> Seq.map (fun fp -> cpDirectCCall fp)
        |> dpBlock


    // Generate function prototypes for implemented functions
    let localFunctions =
        compilations 
        |> List.map (fun c -> c.signature) 
        |> dpBlock
    
    let entryCompilation = 
        compilations |> List.find (fun c -> c.name = entryPoint)

    let programFunctionPrototypes =
        // TODO: The tick function can return a value, not always void, fjg. 18.04.19
        let voidType = (Types.ValueTypes ValueTypes.Void) 
        [ ProgramGenerator.programFunctionProtoype ctx.cliContext.passPrimitiveByAddress (AppName.tick moduleName) entryCompilation.iface voidType
          ProgramGenerator.programFunctionProtoype false (AppName.init moduleName) Iface.Empty voidType
          ProgramGenerator.programFunctionProtoype false (AppName.printState moduleName) entryCompilation.iface voidType ]
        |> dpToplevel
        
    // combine all into one Doc
    [ includeGuardBegin
      Comment.generatedCode
      Comment.blechHeader
      blechHeader
      Comment.userTypes
      userTypes    // all user types are global
      // userConst // only exposed constants and params go there, currently none
      Comment.cPrototypes
      externFunctions
      // directCCalls  // only exposed direct C Calls go there, currently none
      // localFunctions  // only exposed functions go there, currently none

      // TODO: Program functions must not be created and exposed for blech modules, fjg. 18.04.19
      Comment.cProgramFunctions
      programFunctionPrototypes

      includeGuardEnd ]
    |> dpToplevel

// end of cpModuleHeader


/// Emit C code for main app as Doc
/// compilations is required to find the entry point name
//let cpApp ctx (compilations: Compilation list) entryPoint =
let private cpApp (ctx: Arguments.BlechCOptions) (moduleName: SearchPath.ModuleName) (compilations: Compilation list) entryPointName =
    // C header
    let cHeaders = txt "#include <stdio.h>"

    let blechHeader = txt "#include \"blech.h\""
    
    let includeCProgramFile = 
        let hfile = txt <| SearchPath.moduleToCFileInclude moduleName
        txt "#include" <+> dquotes hfile

    // main
    // static variables
    let entryCompilation = compilations |> List.find (fun c -> c.name = entryPointName)
    
    let staticVars = cpMainParametersAsStatics entryCompilation.iface

    let mainLoop = 
        ProgramGenerator.appMainLoop (AppName.init moduleName) 
                                      (AppName.tick moduleName) 
                                      (AppName.printState moduleName)
                                      entryCompilation

    // combine all into one Doc
    [ Comment.generatedCode
      Comment.cheaders
      cHeaders
      Comment.blechHeader
      blechHeader
      Comment.blechCInclude
      includeCProgramFile
      Comment.externalState
      staticVars
      Comment.testFunction
      mainLoop ]
    |> dpToplevel
// end of cpApp

// TODO: Use module name for self include. Remove separate entryPointName param - it is part of package fjg 10.01.19
let public emitCode ctx (package: BlechModule) compilations entryPointName =
    cpModuleCode ctx package.name package.memberPragmas compilations entryPointName
    //|> render (Some 160)
    |> render (Some 80)

// TODO: Remove entryPointName, it is part of package. fjg 10.01.19
let public emitHeader ctx (package: BlechModule) compilations entryPointName =
    cpModuleHeader ctx package.name compilations entryPointName
    //|> render (Some 160)
    |> render (Some 80)

let public emitApp ctx (package: BlechModule) compilations entryPointName =
    cpApp ctx package.name compilations entryPointName
    //|> render (Some 160)
    |> render (Some 80)