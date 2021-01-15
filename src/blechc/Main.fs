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

namespace Blech.Compiler

module Main = 
    open System.IO
    
    open Blech.Common
    open Blech.Frontend
    open Blech.Intermediate
    open Blech.Backend


    type BlechCError = 
            | ModuleNotFound of moduleName: string * triedFiles: string list
        
            interface Diagnostics.IDiagnosable with
            
                member err.MainInformation =
                    match err with
                    | ModuleNotFound (moduleName, triedFiles)->
                        { range = Range.rangeCmdArgs
                          message = sprintf "module '%s' not found" moduleName}
           
                member err.ContextInformation = []
            
                member err.NoteInformation =
                    match err with 
                    | ModuleNotFound (triedFiles = fs) ->
                        List.map (fun f -> sprintf "no file '%s'" f) fs
                

    let private blechcVersion =
        let assembly = System.Reflection.Assembly.GetExecutingAssembly()
        let assemName = assembly.GetName();
        let version = assemName.Version
        sprintf "%d.%d.%d+%d" version.Major version.Minor version.Build version.Revision


    let private blechcCopyright = 
        let assembly = System.Reflection.Assembly.GetExecutingAssembly()
        let attrs = assembly.GetCustomAttributes(typeof<System.Reflection.AssemblyCopyrightAttribute>, true)
        string (attrs.[0] :?> System.Reflection.AssemblyCopyrightAttribute).Copyright


    //---
    //  Functions that run a single compilation phase
    //---

    let private runParser logger implOrIface moduleName contents fileName =
        Logging.log2 "Main" ("processing file " + fileName)
        ParsePkg.parseModuleFromStr logger implOrIface moduleName fileName contents


    let runNameResolution logger moduleName inputFile importedLookupTables importedExportScopes ast =
        Logging.log2 "Main" ("performing name resolution on " + inputFile)
        NameChecking.initialise logger moduleName importedLookupTables importedExportScopes
        |> NameChecking.checkDeclaredness <| ast


    let private runTypeChecking cliArgs logger inputFile otherLuts astAndEnv =
        Logging.log2 "Main" ("performing type checking on " + inputFile)
        TypeChecking.typeCheck cliArgs logger otherLuts astAndEnv


    let private runCausalityCheck logger inputFile tyAstAndLut =
        Logging.log2 "Main" ("checking causality in " + inputFile) 
        Causality.checkPackCausality logger tyAstAndLut


    let runImportCompilation packageContext logger importChain moduleName fileName ast = 
        Logging.log2 "Main" ("checking imports in " + fileName + " and compiling imported modules")
        ImportChecking.checkImports packageContext logger importChain moduleName ast 

    let runSingletonInference logger symboltableEnv fileName importedSingletons ast = 
        Logging.log2 "Main" (sprintf "infer singleton in '%s'" fileName)
        SingletonInference.inferSingletons logger symboltableEnv importedSingletons ast 
            

    let runExportInference logger symboltableEnv fileName importedAbstractTypes importedSingletons ast = 
        Logging.log2 "Main" (sprintf "infer signature for module '%s'" fileName)
        ExportInference.inferExports logger symboltableEnv importedAbstractTypes importedSingletons ast 
        
    //---
    //  Functions that write to the file system during compilation
    //---

    let private writeFile outFileName txt =
        FileInfo(outFileName).Directory.Create()
        do File.WriteAllText(outFileName, txt)


    let private writeSignature outDir moduleName exports ast =
        let signatureFile = Path.Combine(outDir, TranslatePath.moduleToInterfaceFile moduleName)
        let blechSignature = SignaturePrinter.printSignature exports ast
        do writeFile signatureFile blechSignature


    let private writeImplementation outDir moduleName (modul: BlechTypes.BlechModule) importedModules translationContext compilations =
        let codeFile = Path.Combine(outDir, TranslatePath.moduleToCFile moduleName)
        let code = 
            match modul.entryPoint with
            | Some ep ->
                CodeGeneration.emitMainCode translationContext modul importedModules compilations ep.Name
            | None ->
                CodeGeneration.emitCode translationContext modul importedModules compilations
        do writeFile codeFile code


    let private writeHeader outDir moduleName (modul: BlechTypes.BlechModule) importedModules translationContext compilations =
        let headerFile = Path.Combine(outDir, TranslatePath.moduleToHFile moduleName)
        let header = 
            match modul.entryPoint with
            | Some ep ->
                CodeGeneration.emitMainHeader translationContext modul importedModules compilations ep.Name
            | None ->
                CodeGeneration.emitHeader translationContext modul importedModules compilations
        do writeFile headerFile header


    let private possiblyWriteTestApp (cliArgs: Arguments.BlechCOptions) (modul: BlechTypes.BlechModule) translationContext compilations =
        match cliArgs.appName, modul.entryPoint with
        | Some an, Some ep ->
            let appFile = Path.Combine(cliArgs.outDir, TranslatePath.appNameToCFile an)
            let app = CodeGeneration.emitApp translationContext modul compilations ep.Name
            do FileInfo(appFile).Directory.Create()
            do File.WriteAllText(appFile, app)
        | Some _, None // TODO: throw error if there is no entry point, fg 17.09.20
        | None, _ -> 
            ()


    //let private checkImport (packageContext: CompilationUnit.Context<ImportChecking.ModuleInfo>) currentpath (import: AST.Member) = 
    //    let pkgCtx = { packageContext with logger = Diagnostics.Logger.create() }
    //    match import with
    //    | AST.Member.Import i ->
    //        let importPath = i.modulePath.path
    //        CompilationUnit.require pkgCtx i.modulePath.path
    //        //|> Result.map (fun cu -> importPath, cu)
    //        //|> Result.map (fun cu -> i.localName, cu)
    //    | _ ->
    //        failwith "This should never happen"
    
    /// Runs compilation steps given input as a string
    /// which exactly depends on options such as --dry-run
    /// returns a Result type of
    /// TypeCheckContext and typed AST (BlechModule)
    /// or Diagnostic.Logger
    //let compileFromStr cliArgs (pkgCtx: CompilationUnit.Context<SymbolTable.Environment * TypeCheckContext * BlechTypes.BlechModule * TranslationContext>) logger (fromPath: TranslationUnitPath) fileName fileContents =

    let compileFromStr cliArgs (pkgCtx: CompilationUnit.Context<ImportChecking.ModuleInfo>) logger importChain moduleName fileName fileContents =
        // always run lexer, parser, import compilation, name resolution, export inference, type check and causality checks
        
        let astRes = runParser logger CompilationUnit.Implementation moduleName fileContents fileName
        
        let importsRes =
            astRes
            |> Result.bind (runImportCompilation pkgCtx logger importChain moduleName fileName)
                        
        match astRes, importsRes with
        | Ok ast, Ok imports -> 
            
            let astAndSymTableRes =
                // let importedEnvs = imports.GetNameCheckEnvironments // TODO: Take this from the package Context, fjg. 23.10.20
                let lookupTables = imports.GetLookupTables
                let exportScopes = imports.GetExportScopes
                runNameResolution logger moduleName fileName lookupTables exportScopes ast

            let inferredSingletonRes = 
                let importedSingletons = imports.GetSingletons
                astAndSymTableRes 
                |> Result.bind (fun (ast, env) -> runSingletonInference logger env fileName importedSingletons ast)

            let inferredExportRes = 
                let importedAbstractTypes = imports.GetAbstractTypes
                let importedSingletons = imports.GetSingletons
                astAndSymTableRes
                |> Result.bind (fun (ast, env) -> runExportInference logger env fileName importedAbstractTypes importedSingletons ast)
            
            let lutAndPackRes = 
                astAndSymTableRes 
                |> Result.bind (fun (ast, env) -> runTypeChecking cliArgs logger fileName imports.GetTypeCheckContexts (ast, env))
        
            let pgsRes = 
                lutAndPackRes 
                |> Result.bind (runCausalityCheck logger fileName)
            
            match astAndSymTableRes, inferredSingletonRes, inferredExportRes, lutAndPackRes, pgsRes with    
            | Ok (ast, env), Ok singletons, Ok exports, Ok (lut, blechModule), Ok pgs ->
                // generate block graphs for all activities
                // this is only needed for code generation but is left here for debugging purposes
                let blockGraphContext = BlockGraph.bgCtxOfPGs pgs
                let translationContext: TranslationContext =
                    { tcc = lut
                      pgs = pgs
                      bgs = blockGraphContext 
                      compilations = []
                      cliContext = cliArgs }
                        
                let compilations = CodeGeneration.translate translationContext blechModule
                let translationContext = 
                    { translationContext with compilations = compilations @ translationContext.compilations}

                Logging.log6 "Main" ("source code\n")
                for c in compilations do
                    let codetxt = PPrint.PPrint.render (Some 160) c.implementation
                    let msg = sprintf "Code for %s:\n%s\n" c.name.basicId codetxt
                    Logging.log6 "Main" msg

                // if not dry run, write it to file
                // create code depending on entry point
                if not cliArgs.isDryRun then
                    // if not entry point, create signature
                    let isMainProgram = Option.isSome blechModule.entryPoint
                    if not isMainProgram then
                        Logging.log2 "Main" ("writing signature for " + fileName)
                        do writeSignature cliArgs.outDir moduleName exports ast

                    let importedMods = imports.GetTypedModules
                    Logging.log2 "Main" ("writing C code for " + fileName)
                    // implementation should also include headers of imported modules, fjg. 19.10.20
                    do writeImplementation cliArgs.outDir moduleName blechModule importedMods translationContext compilations
                    do writeHeader cliArgs.outDir moduleName blechModule importedMods translationContext compilations
                    
                    // generated test app if required by cliArgs
                    do possiblyWriteTestApp cliArgs blechModule translationContext compilations

                // return interface information and dependencies for module 
                let importedModules = imports.GetImportedModuleNames
                Ok <| ImportChecking.ModuleInfo.Make importedModules env singletons exports lut blechModule

            | _ ->
                // Error during name checking or-else export inference or-else type checking or-else causality checking
                Error <| logger
        | _ ->
            // Error during parsing or else import compilation
            Error <| logger

                
    /// Runs compilation starting with a filename
    let compileFromFile cliArgs pkgCtx logger importChain moduleName inputFile =
        // open stream from file
        File.ReadAllText (Path.GetFullPath(inputFile))
        |> compileFromStr cliArgs pkgCtx logger importChain moduleName inputFile
    

    //let compileInterface (cliContext: Arguments.BlechCOptions) 
    //                     (pkgContext: CompilationUnit.Context<TypeCheckContext * BlechTypes.BlechModule>) 
    //                     diagnosticLogger 
    //                     (fromPath: FromPath.FromPath)
    //                     (inputFile: string) =

    //    let moduleName = fromPath.ToModuleName
        
    //    // parse
    //    Logging.log2 "Main" ("processing source file " + inputFile)
    //    let astRes = 
    //        ParsePkg.parseModuleFromFile diagnosticLogger CompilationUnit.Interface moduleName inputFile
        
    //    // TODO: recurse over signature imports here, fromPath argument is needed here.
    //    // fjg. 24.09.20

    //    // name resolution 
    //    Logging.log2 "Main" ("performing name resolution on " + inputFile)
    //    let astAndEnvRes = 
    //        let ncContext = NameChecking.initialiseEmpty diagnosticLogger moduleName
    //        Result.bind (NameChecking.checkDeclaredness pkgContext ncContext) astRes
        
    //    // type check
    //    Logging.log2 "Main" ("performing type checking on " + inputFile)
    //    let tyAstAndLutRes = 
    //        Result.bind (TypeChecking.typeCheck cliContext) astAndEnvRes
        
    //    //match tyAstAndLutRes with
    //    //| Ok (lut, package) ->        
    //    //    let translationContext: TranslationContext =
    //    //        { tcc = lut
    //    //          pgs = Dictionary()
    //    //          bgs = Dictionary() 
    //    //          cliContext = cliContext }
    //    //    let compilations = translate translationContext package
            
    //    //    // this ensures side-effects (files written) are prevented in a dry run
    //    //    if not cliContext.isDryRun then
    //    //        // TODO: Add exposed subprograms and constants to header, fjg 21.01.19
    //    //        // TODO: Take package into account, fjg 10.01.19
    //    //        let headerFile = Path.Combine(cliContext.outDir, SearchPath.moduleToHFile moduleName)
    //    //        let header = CodeGeneration.emitHeader translationContext package compilations
    //    //        FileInfo(headerFile).Directory.Create()
    //    //        File.WriteAllText(headerFile, header)
    //    //| _ ->
    //    //    ()
    
    //    tyAstAndLutRes

        
    let loader options packageContext logger importChain implOrIface moduleName infile 
            : Result<CompilationUnit.Module<ImportChecking.ModuleInfo>, Diagnostics.Logger> =
        let compilationRes = 
            match implOrIface with
            | CompilationUnit.Implementation ->
                compileFromFile options packageContext logger importChain moduleName infile
            //| CompilationUnit.Interface ->
            //    compileInterface options packageContext logger fromPath infile
                
        Result.bind (CompilationUnit.Module<_>.Make moduleName infile) compilationRes 


    let handleAction (options: Arguments.BlechCOptions) pkgCtx (action: CmdLine.Action) = 
        match action with
        | CmdLine.ShowVersion ->
            printfn "Blech Compiler %s  Copyright (C) %s" blechcVersion blechcCopyright
            Ok ()
        | CmdLine.Compile ->
            let logger = Diagnostics.Logger.create()   
            let inputFile = options.inputFile
            let noImportChain = CompilationUnit.ImportChain.Empty
            CompilationUnit.load pkgCtx logger noImportChain inputFile
            |> Result.bind (fun _ -> Ok ())


    [<EntryPoint>]
    let main (argv : string []) =
        let co = Arguments.collectOptions argv
        match co with
        | Error commandLineHelp ->
            printfn "%s" commandLineHelp 
            -3
        | Ok options ->
            try
                let pkgCtx = CompilationUnit.Context.Make options (loader options)
                
                let cl = CmdLine.processCmdParameters options
                let rw = Result.bind (handleAction options pkgCtx) cl
                match rw with
                | Ok () ->
                    0 
                | Error logger ->
                    Diagnostics.Emitter.printDiagnostics logger
                    // print errors for all imported modules with errors - each has a logger

                    let errImps = pkgCtx.GetErrorImports
                    let printImportDiagnostics (moduleName, logger) =
                        System.Console.Out.WriteLine(sprintf "\nImported Module: \"%s\"\n" <| string moduleName)
                        Diagnostics.Emitter.printDiagnostics logger
                    do List.iter printImportDiagnostics errImps
                    -1
         
            with  e ->
                System.Console.Out.WriteLine ("##### Internal Error: " + e.Message)
                System.Console.Out.WriteLine ("##### Please submit a bug report for Blech " + blechcVersion)
                System.Console.Out.WriteLine e.StackTrace
                -2
