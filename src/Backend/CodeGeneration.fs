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

// Concerning header files we follow:
// http://umich.edu/~eecs381/handouts/CppHeaderFileGuidelines.pdf


open Blech.Common
open Blech.Common.TranslationUnitPath
open Blech.Common.PPrint.PPrint

open Blech.Frontend
open Blech.Frontend.BlechTypes
open Blech.Frontend.PrettyPrint.DocPrint

open CPdataAccess2
open CPrinter
open TraceGenerator


[<RequireQualifiedAccess>]
module Comment =

    let generatedCode =
        cpGeneratedComment <| txt "This is generated code - do not touch!"

    // c file comments

    let cHeaders =
        cpGeneratedComment <| txt "used C headers"
    
    let blechHeader = 
        cpGeneratedComment <| txt "blech types"

    let importHeaders = 
        cpGeneratedComment <| txt "imports"
    
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

    let activityContexts =
        cpGeneratedComment <| txt "activity contexts"
  
    let cPrototypes = 
        cpGeneratedComment <| txt "extern functions to be implemented in C"

    let exportedFunctions =
        cpGeneratedComment <| txt "exported functions"
    
    let userTypes = 
        cpGeneratedComment <| txt "all user defined types"

    let cProgramFunctions =
        cpGeneratedComment <| txt "program functions: tick, init"

    let cTraceFunction =
        cpGeneratedComment <| txt "trace function: printState"

    // app file comments

    let blechCInclude = 
        cpGeneratedComment <| txt "the generated blech program"
    
    let externalState =
        cpGeneratedComment <| txt "external state for the blech program"

    let testFunction = 
        cpGeneratedComment <| txt "the test main loop"


/// Translates all sub programs of a module into a list of compilations
let public translate ctx (pack: BlechModule) =
    // translate all subprograms in order
    pack.funacts
    |> List.fold (fun compilations funact ->
        if funact.IsFunction then FunctionTranslator.translate ctx funact
        else ActivityTranslator.translate ctx funact
        |> List.singleton
        |> List.append compilations) []


/// Common header definitions
let stdioHeader = txt "#include <stdio.h>"

let programHeader = txt "#include <string.h>"

let includeQuotedHfile hfile = 
    txt "#include" <+> (txt hfile |> dquotes)

let blechHeader = includeQuotedHfile "blech.h"

let generateSelfHeader =
    TranslatePath.moduleToInclude >> includeQuotedHfile
        
let generateCProgramHeader =
    TranslatePath.moduleToCFileInclude >> includeQuotedHfile

let generateIncludeGuards moduleName =
    let guard = txt <| TranslatePath.moduleToIncludeGuard moduleName
    let includeGuardBegin = 
        txt "#ifndef" <+> guard
        <.> txt "#define" <+> guard
    let includeGuardEnd = 
        txt "#endif" <+> enclose (txt "/* ", txt " */") guard
    includeGuardBegin, includeGuardEnd

let generateSubmoduleIncludes otherMods =
    otherMods
    |> List.map (fun otherMod -> TranslatePath.moduleToInclude otherMod.name |> includeQuotedHfile)
    |> dpBlock

/// Emit C code for module as Doc
let private cpModuleCode ctx (moduleName: TranslationUnitPath) 
                             (pragmas: Attribute.MemberPragma list) 
                             importedModules
                             (compilations: Compilation list) 
                             entryPointOpt =

    let selfHeader = generateSelfHeader moduleName
        
    // Blech const become #define macros in C
    // right now all go to the module code, because nothing gets exported
    // constants local to subprograms should also work

    let varDecls = 
        ctx.tcc.nameToDecl.Values
        |> Seq.choose (fun d -> match d with | Declarable.VarDecl f -> Some f | _ -> None)

    let externConsts = 
        ctx.tcc.nameToDecl.Values
        |> Seq.choose (fun d -> match d with | Declarable.ExternalVarDecl f -> Some f | _ -> None)
    
    /// C define macros for external constants / params
    /// e.g. #define blc_MyActivity_myConst &FOO(BAR)
    let externConstMacros = 
        let renderExternConst (ec: ExternalVarDecl) = 
            let cexpr = 
                match ec.annotation.cvardecl with
                | Some (Attribute.CConst (binding = text))
                | Some (Attribute.CParam (binding = text)) ->
                    txt text |> parens
                | _ -> 
                    failwith "This should never happen"            
            
            let macro = 
                txt "#define" <+> (renderCName Current ctx.tcc ec.name) <+> cexpr
                |> groupWith (txt " \\")
            
            cpOptDocComments ec.annotation.doc
            |> dpOptLinePrefix <| macro

        externConsts
        |> Seq.filter (fun extVar -> match extVar.mutability with Mutability.CompileTimeConstant | Mutability.StaticParameter -> true | _ -> false)
        |> Seq.map renderExternConst
        |> dpBlock

    let userParams =
        let renderParam (v: VarDecl) =
            let {prereqStmts=prereqStmts; cExpr=cExpr} = cpExpr ctx.tcc v.initValue
            let vname = (cpName (Some Current) ctx.tcc v.name).Render
            assert (List.length prereqStmts = 0)
            let decl = txt "static" <+> cpArrayDeclDoc vname v.datatype <+> txt "=" <+> cExpr.Render <^> semi

            cpOptDocComments v.annotation.doc
            |> dpOptLinePrefix
            <| decl

        varDecls
        |> Seq.filter (fun vd -> vd.mutability.Equals Mutability.StaticParameter)
        |> Seq.map renderParam
        |> dpBlock

    // Translate function prototypes to direct C calls
    let functionPrototypes = 
        ctx.tcc.nameToDecl.Values
        |> Seq.choose (fun d -> match d with | Declarable.ProcedurePrototype f -> Some f | _ -> None)
    
    let cCalls =
        Seq.filter (fun (fp: ProcedurePrototype) -> fp.IsDirectCCall) functionPrototypes

    let cHeaders = 
        let cCalls = Seq.choose (fun (fp: ProcedurePrototype) -> fp.annotation.TryGetCHeader) cCalls
        let extConsts = Seq.choose (fun (vd: ExternalVarDecl) -> vd.annotation.TryGetCHeader) externConsts
        let cIncludes = List.choose (fun (mp: Attribute.MemberPragma) -> mp.TryGetCHeader) pragmas

        seq {extConsts; cCalls; cIncludes }
        |> Seq.concat 
        |> Seq.distinct
        |> Seq.map includeQuotedHfile
        |> dpBlock
    
    let importIncludes = generateSubmoduleIncludes importedModules
    
    let directCCalls = 
        cCalls
        |> Seq.map (fun fp -> cpDirectCCall ctx.tcc fp)
        |> dpToplevel

    // Translated subprograms
    let code = 
        compilations 
        |> List.map (fun c -> dpOptLinePrefix c.doc c.implementation) 
        |> dpToplevel

    // only relevant for main (entry point) programs - not modules
    let globVars, mainCallback, mainInit, printState =
        match entryPointOpt with
        | None -> empty, empty, empty, empty
        | Some entryPoint ->
            let entryCompilation = compilations |> List.find (fun c -> c.name = entryPoint)
            (
                // global variables
                cpMainStateAsStatics entryCompilation,
                // tick function
                ProgramGenerator.mainCallback ctx.tcc ctx.cliContext.passPrimitiveByAddress 
                                              (AppName.tick moduleName) 
                                              entryCompilation.name 
                                              entryCompilation,
                // init function
                ProgramGenerator.mainInit ctx (AppName.init moduleName) entryCompilation,
                // state printer
                ProgramGenerator.printState ctx (AppName.printState moduleName) entryCompilation
            )
            // just an idea how to determine static memory usage
            //let printStatistics =
            //    """
            //    void blc_blech_ScatteredLocals_printStats() {
            //        printf("Context size: %d bytes\n", sizeof blc_blech_ctx);
            //    }
            //    """ |> txt
        
    
    // combine all into one Doc
    [ Comment.generatedCode
      programHeader
      (if ctx.cliContext.trace then stdioHeader else empty)
      Comment.cHeaders
      cHeaders
      Comment.blechHeader
      blechHeader
      
      // Guideline #12 in http://umich.edu/~eecs381/handouts/CppHeaderFileGuidelines.pdf
      Comment.selfInclude
      selfHeader
      Comment.importHeaders 
      importIncludes 

      Comment.cConstants
      externConstMacros
      Comment.cFunctions
      directCCalls
      //Comment.constants
      //userConst
      Comment.parameters
      userParams
      if entryPointOpt.IsSome then
          Comment.state
          globVars
      Comment.compilations
      code
      (if ctx.cliContext.trace then genStatePrinters ctx.tcc compilations entryPointOpt else empty)
      if entryPointOpt.IsSome then
          Comment.progam
          mainCallback
          mainInit
          (if ctx.cliContext.trace then printState else empty) ]
    |> dpRemoveEmptyLines
    |> dpToplevel

// end of cpModuleCode

/// Emit C header for module as Doc
let private cpModuleHeader ctx (moduleName: TranslationUnitPath) importedModules (compilations: Compilation list) entryPointOpt =
    // C header
    let includeGuardBegin, includeGuardEnd = generateIncludeGuards moduleName
    
    let importIncludes = generateSubmoduleIncludes importedModules

    // Translate function prototypes to extern functions and direct C calls
    let functionPrototypes = 
        ctx.tcc.nameToDecl.Values
        |> Seq.choose (fun d -> match d with | Declarable.ProcedurePrototype f -> Some f | _ -> None)
    
    let cCalls =
        Seq.filter (fun (fp: ProcedurePrototype) -> fp.IsDirectCCall) functionPrototypes

    let cWrappers = 
        Seq.except cCalls functionPrototypes

    let cCallHeaders = 
        let hfiles =
            cCalls
            |> Seq.choose(fun fp -> fp.annotation.TryGetCHeader) 
            |> Seq.distinct
        
        let includeHfile hfile = 
            txt "#include" <+> (txt hfile |> dquotes)
        
        Seq.map includeHfile hfiles
        |> dpBlock

    // Type Declarations
    let userTypes = 
        ctx.tcc.userTypes
        |> Seq.choose (fun kvp -> if kvp.Key.moduleName = moduleName then Some kvp.Value else None) // make sure only this module's types are printed
        |> Seq.map (snd >> cpUserType)
        |> dpBlock

    // Activity Contexts
    let activityContexts =
        List.map cpContextTypeDeclaration compilations
        |> dpBlock

    let externFunctions =
        let ifaceOf (fp: ProcedurePrototype) =
            {Compilation.mkNew fp.name with inputs = fp.inputs; outputs = fp.outputs}
        cWrappers
        |> Seq.toList // change to List for eager evaluation since ctx.tcc may be updated during the map iteration
        |> List.map (fun fp -> cpExternFunction ctx.tcc fp.annotation.doc fp.name (ifaceOf fp) (fp.returns) )
        |> dpToplevel

    let directCCalls = // TODO: directCCalls must not be exported, check this, fjg. 20.02.19
        cCalls
        |> Seq.map (fun fp -> cpDirectCCall ctx.tcc fp)
        |> dpBlock


    // Generate function prototypes for implemented functions
    let localFunctions =
        compilations 
        |> List.map (fun c -> c.signature) 
        |> dpBlock
    
    let programFunctionPrototypes, traceFunctionPrototype =
        match entryPointOpt with
        | None -> empty, empty // no entry point means we are compiling a module, nothing to do here
        | Some entryPoint ->   // we have a main program and thus need tick function etc...
            let entryCompilation = 
                compilations |> List.find (fun c -> c.name = entryPoint)
            let progFunProt =
                // TODO: The tick function can return a value, not always void, fjg. 18.04.19
                let qname = AppName.init moduleName
                let voidType = (ValueTypes ValueTypes.Void) 
                [ ProgramGenerator.programFunctionPrototype ctx.tcc ctx.cliContext.passPrimitiveByAddress (AppName.tick moduleName) entryCompilation voidType
                  ProgramGenerator.programFunctionPrototype ctx.tcc false qname (Compilation.mkNew qname) voidType
                  ProgramGenerator.programFunctionPrototype ctx.tcc false (AppName.printState moduleName) entryCompilation voidType ]
                |> dpToplevel
            let traceFunProt =
                let voidType = (ValueTypes ValueTypes.Void)
                [ ProgramGenerator.programFunctionPrototype ctx.tcc false (AppName.printState moduleName) entryCompilation voidType ]
                |> dpToplevel
            progFunProt, traceFunProt

    // combine all into one Doc
    [ includeGuardBegin
      Comment.generatedCode
      Comment.blechHeader
      blechHeader
      Comment.importHeaders
      importIncludes
      Comment.userTypes
      userTypes    // all user types are global
      Comment.activityContexts
      activityContexts
      
      // Comment.constants
      // userConst // only exposed constants and params go there, currently none
      
      // Comment.parameters
      // userParams // only exposed params go there, currently non
      
      // Comment.constants
      
      Comment.cPrototypes
      externFunctions
      
      Comment.cConstants
      // externConstMacros
      
      Comment.cFunctions
      // directCCalls  // only exposed direct C Calls go there, currently none
      
      Comment.exportedFunctions
      // localFunctions // only exposed functions go there, currently all

      // Program functions must not be created and exposed for blech modules
      if entryPointOpt.IsSome then
          Comment.cProgramFunctions
          programFunctionPrototypes

          (if ctx.cliContext.trace then
            [ Comment.cTraceFunction
              traceFunctionPrototype ]
            |> dpToplevel
           else empty)
      includeGuardEnd ]
    |> dpRemoveEmptyLines
    |> dpToplevel

// end of cpModuleHeader

/// Emit C code for main app as Doc
/// compilations is required to find the entry point name
let private cpApp ctx (moduleName: TranslationUnitPath) (compilations: Compilation list) entryPointName =
    let includeCProgramFile = generateCProgramHeader moduleName
        
    let entryCompilation = compilations |> List.find (fun c -> c.name = entryPointName)
    
    // inputs and outputs of the entry point (are not part of the internal Blech state)
    let staticVars = cpMainParametersAsStatics ctx.tcc entryCompilation

    let mainLoop = 
        ProgramGenerator.appMainLoop ctx (AppName.init moduleName)
                                      (AppName.tick moduleName) 
                                      (AppName.printState moduleName)
                                      entryCompilation

    // combine all into one Doc
    [ Comment.generatedCode
      Comment.cHeaders
      (if ctx.cliContext.trace then stdioHeader else empty)
      Comment.blechHeader
      blechHeader
      Comment.blechCInclude
      includeCProgramFile
      Comment.externalState
      staticVars
      Comment.testFunction
      mainLoop ]
    |> dpRemoveEmptyLines
    |> dpToplevel
// end of cpApp


// TODO: Use module name for self include. Remove separate entryPointName param - it is part of package fjg 10.01.19
let public emitCode ctx (modul: BlechModule) importedModules compilations =
    cpModuleCode ctx modul.name modul.memberPragmas importedModules compilations None
    |> render (Some 80)

let public emitMainCode ctx (modul: BlechModule) importedModules compilations entryPointName =
    cpModuleCode ctx modul.name modul.memberPragmas importedModules compilations (Some entryPointName)
    |> render (Some 80)

// TODO: Remove entryPointName, it is part of package. fjg 10.01.19
let public emitHeader ctx (modul: BlechModule) importedModules compilations =
    cpModuleHeader ctx modul.name importedModules compilations None
    |> render (Some 80)

let public emitMainHeader ctx (modul: BlechModule) importedModules compilations entryPointName =
    cpModuleHeader ctx modul.name importedModules compilations (Some entryPointName)
    |> render (Some 80)

let public emitApp ctx (modul: BlechModule) compilations entryPointName =
    cpApp ctx modul.name compilations entryPointName
    //|> render (Some 160)
    |> render (Some 80)