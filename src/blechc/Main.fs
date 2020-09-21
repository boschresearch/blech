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
    open Blech.Backend.CodeGeneration


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
        
    let private runParser logger implOrIface moduleName contents fileName =
        Logging.log2 "Main" ("processing file " + fileName)
        ParsePkg.parseModuleFromStr logger implOrIface moduleName contents fileName

    let private runNameResolution logger pkgCtx moduleName inputFile ast =
        Logging.log2 "Main" ("performing name resolution on " + inputFile)
        NameChecking.initialise logger moduleName
        |> NameChecking.checkDeclaredness pkgCtx <| ast

    let private runTypeChecking cliArgs inputFile astAndEnv =
        Logging.log2 "Main" ("performing type checking on " + inputFile)
        TypeChecking.typeCheck cliArgs astAndEnv

    let private runCausalityCheck inputFile tyAstAndLut =
        Logging.log2 "Main" ("checking causality in " + inputFile) 
        Causality.checkPackCausality tyAstAndLut

    let private writeFile outFileName txt =
        FileInfo(outFileName).Directory.Create()
        File.WriteAllText(outFileName, txt)

    let private writeSignature outDir moduleName ncEnv ast =
        let signatureFile = Path.Combine(outDir, SearchPath.moduleToInterfaceFile moduleName)
        let blechSignature = SignaturePrinter.printSignature ncEnv ast
        writeFile signatureFile blechSignature

    let private writeImplementation outDir moduleName (blechModule: BlechTypes.BlechModule) translationContext compilations =
        let codeFile = Path.Combine(outDir, SearchPath.moduleToCFile moduleName)
        let code = 
            match blechModule.entryPoint with
            | Some ep ->
                CodeGeneration.emitMainCode translationContext blechModule compilations ep.name
            | None ->
                CodeGeneration.emitCode translationContext blechModule compilations
        writeFile codeFile code

    let private writeHeader outDir moduleName (blechModule: BlechTypes.BlechModule) translationContext compilations =
        let headerFile = Path.Combine(outDir, SearchPath.moduleToHFile moduleName)
        let header = 
            match blechModule.entryPoint with
            | Some ep ->
                CodeGeneration.emitMainHeader translationContext blechModule compilations ep.name
            | None ->
                CodeGeneration.emitHeader translationContext blechModule compilations
        writeFile headerFile header

    let private possiblyWriteTestApp (cliArgs: Arguments.BlechCOptions) (blechModule: BlechTypes.BlechModule) translationContext compilations =
        match cliArgs.appName, blechModule.entryPoint with
        | Some an, Some ep ->
            let appFile = Path.Combine(cliArgs.outDir, SearchPath.appNameToCFile an)
            let app = CodeGeneration.emitApp translationContext blechModule compilations ep.name
            FileInfo(appFile).Directory.Create()
            File.WriteAllText(appFile, app)
        | Some _, None // TODO: throw error if there is no entry point, fg 17.09.20
        | None, _ -> 
            ()
    
    /// Runs compilation steps given input as a string
    /// which exactly depends on options such as --dry-run
    /// returns a Result type of
    /// TypeCheckContext and typed AST (BlechModule)
    /// or Diagnostic.Logger
    let compileFromStr cliArgs pkgCtx logger moduleName fileName fileContents =
        // always run lexer, parser, name resolution, type check and causality checks
        let astRes = runParser logger Package.Implementation moduleName fileContents fileName
        let astAndSymTableRes = astRes |> Result.bind (runNameResolution logger pkgCtx moduleName fileName)
        let lutAndPackRes = astAndSymTableRes |> Result.bind (runTypeChecking cliArgs fileName)
        let pgsRes = lutAndPackRes |> Result.bind (runCausalityCheck fileName)
        match astAndSymTableRes, lutAndPackRes, pgsRes with
        | _, _, Error logger
        | _, Error logger, _                  // the last two cases just
        | Error logger, _, _ -> Error logger  // satisfy the F# compiler
        | Ok (ast, symTable), Ok (lut, blechModule), Ok pgs ->
            // generate block graphs for all activities
            // this is only needed for code generation but is left here for debugging purposes
            let blockGraphContext = BlockGraph.bgCtxOfPGs pgs
            let translationContext: TranslationContext =
                { tcc = lut
                  pgs = pgs
                  bgs = blockGraphContext 
                  cliContext = cliArgs }
                        
            let compilations = translate translationContext blechModule

            Logging.log6 "Main" ("source code\n")
            for c in compilations do
                let codetxt = PPrint.PPrint.render (Some 160) c.implementation
                let msg = sprintf "Code for %s:\n%s\n" c.name.basicId codetxt
                Logging.log6 "Main" msg

            // if not dry run, write it to file
            // create code depending on entry point
            if not cliArgs.isDryRun then
                let isMainProgram = Option.isSome blechModule.entryPoint
                
                // if not entry point, create signature
                if not isMainProgram then
                    Logging.log2 "Main" ("writing signature for " + fileName)
                    writeSignature cliArgs.outDir moduleName lut.ncEnv ast

                Logging.log2 "Main" ("writing C code for " + fileName)
                writeImplementation cliArgs.outDir moduleName blechModule translationContext compilations

                writeHeader cliArgs.outDir moduleName blechModule translationContext compilations

                // generated test app if required by cliArgs
                possiblyWriteTestApp cliArgs blechModule translationContext compilations

            // return interface information for module
            Ok (lut, blechModule)
                        
                
    /// Runs compilation starting with a filename
    let compileFromFile cliArgs pkgCtx logger moduleName inputFile =
        // open stream from file
        File.ReadAllText (Path.GetFullPath(inputFile))
        |> compileFromStr cliArgs pkgCtx logger moduleName inputFile
    

    let compileInterface (cliContext: Arguments.BlechCOptions) 
                         (pkgContext: Package.Context<TypeCheckContext * BlechTypes.BlechModule>) 
                         diagnosticLogger 
                         (moduleName: SearchPath.ModuleName)
                         (inputFile: string) =

        // parse
        Logging.log2 "Main" ("processing source file " + inputFile)
        let astRes = 
            ParsePkg.parseModule diagnosticLogger Package.Interface moduleName inputFile
        
        // name resolution 
        Logging.log2 "Main" ("performing name resolution on " + inputFile)
        let astAndEnvRes = 
            let ncContext = NameChecking.initialise diagnosticLogger moduleName
            Result.bind (NameChecking.checkDeclaredness pkgContext ncContext) astRes
        
        // type check
        Logging.log2 "Main" ("performing type checking on " + inputFile)
        let tyAstAndLutRes = 
            Result.bind (TypeChecking.typeCheck cliContext) astAndEnvRes
        
        //match tyAstAndLutRes with
        //| Ok (lut, package) ->        
        //    let translationContext: TranslationContext =
        //        { tcc = lut
        //          pgs = Dictionary()
        //          bgs = Dictionary() 
        //          cliContext = cliContext }
        //    let compilations = translate translationContext package
            
        //    // this ensures side-effects (files written) are prevented in a dry run
        //    if not cliContext.isDryRun then
        //        // TODO: Add exposed subprograms and constants to header, fjg 21.01.19
        //        // TODO: Take package into account, fjg 10.01.19
        //        let headerFile = Path.Combine(cliContext.outDir, SearchPath.moduleToHFile moduleName)
        //        let header = CodeGeneration.emitHeader translationContext package compilations
        //        FileInfo(headerFile).Directory.Create()
        //        File.WriteAllText(headerFile, header)
        //| _ ->
        //    ()
    
        tyAstAndLutRes
        

    let loader options logger packageContext implOrIface moduleName infile : Result<Package.Module<TypeCheckContext * BlechTypes.BlechModule>, Diagnostics.Logger> =
        let compilationRes = 
            match implOrIface with
            | Package.Implementation ->
                compileFromFile options packageContext logger moduleName infile
            | Package.Interface ->
                compileInterface options packageContext logger moduleName infile
                
        Result.bind (Package.Module<TypeCheckContext * BlechTypes.BlechModule>.Make moduleName infile) compilationRes 

    let compile (options: Arguments.BlechCOptions) logger =
        let inputFile = options.inputFile
        let pkgCtx = Package.Context.Make options logger (loader options logger)
        Package.load pkgCtx inputFile
        // Module.require pkgCtx moduleName
            
        
    let handleAction (options: Arguments.BlechCOptions) (action: CmdLine.Action) = 
        match action with
        | CmdLine.ShowVersion ->
            printfn "Blech Compiler %s  Copyright (C) %s" blechcVersion blechcCopyright
            Ok ()

        | CmdLine.Compile ->
            let logger = Diagnostics.Logger.create()   
            let compiledModule = compile options logger
            Result.bind (fun _ -> Ok ()) compiledModule

    [<EntryPoint>]
    let main (argv : string []) =
        let co = Arguments.collectOptions argv
        match co with
        | Error commandLineHelp ->
            printfn "%s" commandLineHelp 
            -3
        | Ok options ->
            try
                let cl = CmdLine.processCmdParameters options
                let rw = Result.bind (handleAction options) cl 
                match rw with
                | Ok _ ->
                    0 
                | Error logger ->
                    Diagnostics.Emitter.printDiagnostics logger
                    -1
         
            with  e ->
                System.Console.Out.WriteLine ("##### Internal Error: " + e.Message)
                System.Console.Out.WriteLine ("##### Please submit a bug report for Blech " + blechcVersion)
                System.Console.Out.WriteLine e.StackTrace
                -2
