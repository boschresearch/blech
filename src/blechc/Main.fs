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


    let private runTypeChecking cliArgs logger inputFile otherLuts ast env =
        Logging.log2 "Main" ("performing type checking on " + inputFile)
        TypeChecking.typeCheck cliArgs logger otherLuts ast env


    let private runCausalityCheck logger inputFile tyCtx blechModule =
        Logging.log2 "Main" ("checking causality in " + inputFile) 
        Causality.checkPackCausality logger tyCtx blechModule


    let runImportCompilation packageContext logger importChain moduleName fileName ast = 
        Logging.log2 "Main" ("checking imports in " + fileName + " and compiling imported modules")
        ImportChecking.checkImports packageContext logger importChain moduleName ast 

    let runSingletonInference logger fileName importedSingletons ast symboltableEnv = 
        Logging.log2 "Main" (sprintf "infer singleton in '%s'" fileName)
        SingletonInference.inferSingletons logger symboltableEnv importedSingletons ast 
            

    let private runExportInference logger symboltableEnv fileName singletons ast = 
        Logging.log2 "Main" (sprintf "infer signature for module '%s'" fileName)
        ExportInference.inferExports logger symboltableEnv singletons ast 
        
    //---
    //  Functions that write to the file system during compilation
    //---

    let private writeFile outFileName txt =
        FileInfo(outFileName).Directory.Create()
        do File.WriteAllText(outFileName, txt)


    let private writeSignature moduleName exports ast =  
        let signatureFile = TranslatePath.moduleToInterfaceFile moduleName
        let blechSignature = SignaturePrinter.printSignature exports ast
        do writeFile signatureFile blechSignature


    let private writeImplementation outDir moduleName (modul: BlechTypes.BlechModule) importedModules translationContext compilations =
        let codeFile = Path.Combine(outDir, TranslatePath.moduleToCFile moduleName)
        let code = CodeGeneration.emitCode translationContext modul importedModules compilations    
        do writeFile codeFile code


    let private writeHeader outDir moduleName (modul: BlechTypes.BlechModule) importedModules translationContext compilations =
        let headerFile = Path.Combine(outDir, TranslatePath.moduleToHFile moduleName)
        let header = CodeGeneration.emitHeader translationContext modul importedModules compilations    
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


    /// Runs compilation steps given input file as a string
    /// which exactly depends on options such as --dry-run
    /// returns a Result type of
    /// ModuleInfo
    /// or Diagnostic.Logger
    let compileFromStr cliArgs (pkgCtx: CompilationUnit.Context<ImportChecking.ModuleInfo>) logger importChain moduleName fileName fileContents =
        // always run lexer, parser, import compilation, name resolution, export inference, type check and causality checks
        let resultWorkflow = ResultBuilder()
        resultWorkflow
            {
                let! ast =
                    runParser 
                        logger 
                        CompilationUnit.Blc
                        moduleName 
                        fileContents 
                        fileName

                let! imports =
                    runImportCompilation 
                        pkgCtx 
                        logger 
                        importChain 
                        moduleName 
                        fileName
                        ast
                        
                let! symTable =
                    runNameResolution 
                        logger 
                        moduleName 
                        fileName 
                        imports.GetLookupTables
                        imports.GetExportScopes
                        ast

                let! inferredSingleton = 
                    runSingletonInference 
                        logger 
                        fileName 
                        imports.GetSingletons 
                        ast
                        symTable

                let! inferredExport = 
                    runExportInference 
                        logger 
                        symTable 
                        fileName 
                        inferredSingleton 
                        ast

                let! lut, blechModule = 
                    runTypeChecking 
                        cliArgs 
                        logger 
                        fileName 
                        imports.GetTypeCheckContexts 
                        ast 
                        symTable

                let! pgs = 
                    runCausalityCheck 
                        logger 
                        fileName
                        lut 
                        blechModule

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
                compilations 
                |> List.iter (fun c ->
                    let codetxt = PPrint.PPrint.render (Some 160) c.implementation
                    let msg = sprintf "Code for %s:\n%s\n" c.name.basicId codetxt
                    Logging.log6 "Main" msg )

                // if not entry point, create signature
                do  
                    let isMainProgram = Option.isSome blechModule.entryPoint
                    if not isMainProgram then
                        Logging.log2 "Main" ("writing signature for " + fileName)
                        do writeSignature moduleName inferredExport ast
                        
                // if not dry run, write it to file
                // create code depending on entry point
                do // this do is required in a workflow, otherwise a Result<_> type expr is expected
                    if not cliArgs.isDryRun then
                        // if not entry point, create signature
                        //let isMainProgram = Option.isSome blechModule.entryPoint
                        //if not isMainProgram then
                        //    Logging.log2 "Main" ("writing signature for " + fileName)
                        //    do writeSignature cliArgs.outDir moduleName inferredExport ast

                        let importedMods = imports.GetTypedModules
                        Logging.log2 "Main" ("writing C code for " + fileName)
                        // implementation should also include headers of imported modules, fjg. 19.10.20
                        do writeImplementation cliArgs.outDir moduleName blechModule importedMods translationContext compilations
                        do writeHeader cliArgs.outDir moduleName blechModule importedMods translationContext compilations
                    
                        // generated test app if required by cliArgs
                        do possiblyWriteTestApp cliArgs blechModule translationContext compilations

                // return interface information and dependencies for module 
                let importedModules = imports.GetImportedModuleNames
                return ImportChecking.ModuleInfo.Make importedModules symTable inferredSingleton lut blechModule
            }

                
    /// Runs compilation starting with a filename
    let compileFromFile cliArgs pkgCtx logger importChain moduleName inputFile =
        // open stream from file
        File.ReadAllText (Path.GetFullPath(inputFile))
        |> compileFromStr cliArgs pkgCtx logger importChain moduleName inputFile
    

    /// Runs interface compilation steps given input file as a string
    /// returns a Result type of
    /// ModuleInfo
    /// or Diagnostic.Logger
    let compileInterfaceFromStr cliArgs (pkgCtx: CompilationUnit.Context<ImportChecking.ModuleInfo>) logger importChain moduleName fileName fileContents =
        // always run lexer, parser, import compilation, name resolution, export inference, type check and causality checks
        let resultWorkflow = ResultBuilder ()
        resultWorkflow
            {
                let! ast =
                    runParser 
                        logger 
                        CompilationUnit.Blh
                        moduleName 
                        fileContents 
                        fileName

                let! imports =
                    runImportCompilation 
                        pkgCtx 
                        logger 
                        importChain 
                        moduleName 
                        fileName
                        ast
                        
                let! symTable =
                    runNameResolution 
                        logger 
                        moduleName 
                        fileName 
                        imports.GetLookupTables
                        imports.GetExportScopes
                        ast

                let! inferredSingleton = 
                    runSingletonInference 
                        logger 
                        fileName 
                        imports.GetSingletons 
                        ast
                        symTable

                //    no runExportInference 
                
                let! lut, blechModule = 
                    runTypeChecking 
                        cliArgs 
                        logger 
                        fileName 
                        imports.GetTypeCheckContexts 
                        ast 
                        symTable

                let importedModules = imports.GetImportedModuleNames
                
                return ImportChecking.ModuleInfo.Make importedModules symTable inferredSingleton lut blechModule
            }


    /// Runs interface compilation starting with a filename
    let compileInterfaceFromFile cliArgs pkgCtx logger importChain moduleName inputFile =
        // open stream from file
        File.ReadAllText (Path.GetFullPath(inputFile))
        |> compileInterfaceFromStr cliArgs pkgCtx logger importChain moduleName inputFile
    
        
    let loader options packageContext logger importChain implOrIface moduleName infile 
            : Result<CompilationUnit.Module<ImportChecking.ModuleInfo>, Diagnostics.Logger> =
        let compilationRes = 
            match implOrIface with
            | CompilationUnit.Blc->
                printfn "Compile implementation: '%s'" infile
                compileFromFile options packageContext logger importChain moduleName infile
            | CompilationUnit.Blh ->
                printfn "Compile interface: '%s'" infile
                compileInterfaceFromFile options packageContext logger importChain moduleName infile
                
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
