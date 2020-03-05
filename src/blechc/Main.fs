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

    exception FatalError // Temporary. Remove this.

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
                

    let blechcVersion =
        let assembly = System.Reflection.Assembly.GetExecutingAssembly()
        let assemName = assembly.GetName();
        let version = assemName.Version
        sprintf "%d.%d.%d+%d" version.Major version.Minor version.Build version.Revision

    let blechcCopyright = 
        let assembly = System.Reflection.Assembly.GetExecutingAssembly()
        let attrs = assembly.GetCustomAttributes(typeof<System.Reflection.AssemblyCopyrightAttribute>, true)
        string (attrs.[0] :?> System.Reflection.AssemblyCopyrightAttribute).Copyright
        
    //let private compileFrontend (cliContext: Arguments.BlechCOptions) 
    //                            (pkgContext: Package.Context<TypeCheckContext * BlechTypes.BlechModule>) 
    //                            diagnosticLogger 
    //                            (loadWhat: Package.LoadWhat) 
    //                            (moduleName: SearchPath.ModuleName)
    //                            (inputFile: string) =
    //    // parse
    //    Logging.log2 "Main" ("processing source file " + inputFile)
    //    let astRes = 
    //        ParsePkg.parseModule diagnosticLogger loadWhat moduleName inputFile
        
    //    // name resolution 
    //    Logging.log2 "Main" ("performing name resolution on " + inputFile)
    //    let astAndEnvRes = 
    //        let ncContext = NameChecking.initialise diagnosticLogger moduleName
    //        Result.bind (NameChecking.checkDeclaredness pkgContext ncContext) astRes
        
    //    // type check
    //    Logging.log2 "Main" ("performing type checking on " + inputFile)
    //    let tyAstAndLutRes = 
    //        Result.bind TypeChecking.typeCheck astAndEnvRes
        
    //    tyAstAndLutRes
    

    let compileInterface (cliContext: Arguments.BlechCOptions) 
                         (pkgContext: Package.Context<TypeCheckContext * BlechTypes.BlechModule>) 
                         diagnosticLogger 
                         (loadWhat: Package.LoadWhat) 
                         (moduleName: SearchPath.ModuleName)
                         (inputFile: string) =

        // parse
        Logging.log2 "Main" ("processing source file " + inputFile)
        let astRes = 
            ParsePkg.parseModule diagnosticLogger loadWhat moduleName inputFile
        
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
        

    let compileImplementation (cliContext: Arguments.BlechCOptions) 
                              (pkgContext: Package.Context<TypeCheckContext * BlechTypes.BlechModule>) 
                              diagnosticLogger 
                              (loadWhat: Package.LoadWhat) 
                              (moduleName: SearchPath.ModuleName)
                              (inputFile: string) =

        // parse
        Logging.log2 "Main" ("processing source file " + inputFile)
        let astRes = 
            ParsePkg.parseModule diagnosticLogger loadWhat moduleName inputFile
        
        // name resolution 
        Logging.log2 "Main" ("performing name resolution on " + inputFile)
        let astAndEnvRes =
            let ncCtx = NameChecking.initialise diagnosticLogger moduleName
            Result.bind (NameChecking.checkDeclaredness pkgContext ncCtx) astRes
        
        // type check
        Logging.log2 "Main" ("performing type checking on " + inputFile)
        let tyAstAndLutRes = 
            Result.bind (TypeChecking.typeCheck cliContext) astAndEnvRes

        // check there is an entry point
        //match package.entryPoint with
        //| None -> // TODO, adapt causality analysis to run regardless of the entry point, fg 20.11.18
        //    failwith "No entry point given. Please annotate one activity with @[EntryPoint]"
        //| Some _ -> ()
    
        // create program graphs and check their causality
        Logging.log2 "Main" ("checking causality in " + inputFile) 
        let causalityCheckRes =
            Result.bind Causality.checkPackCausality tyAstAndLutRes
        
        match causalityCheckRes with
        | Error logger ->
            Error logger 
        | Ok pgs -> 
            let lut, package = 
                match tyAstAndLutRes with
                | Ok (l, p) ->
                    l, p
                | Error _ ->
                    failwith "this cannot happen"
            
            // generate block graphs for all activities
            // this is only needed for code generation but is left here for debugging purposes
            let blockGraphContext = BlockGraph.bgCtxOfPGs pgs
            
            // instead of printing the unscheduled block graph,
            // we print the scheduled one from the activity translator
            //for g in blockGraphContext do
            //    Logging.log4 "Main" ("block graph\n" + g.Value.blockGraph.ToString())
            
            let translationContext: TranslationContext =
                { tcc = lut
                  pgs = pgs
                  bgs = blockGraphContext 
                  cliContext = cliContext }
            let compilations = translate translationContext package
            
            
            // this ensures side-effects (files written) are prevented in a dry run
            if not cliContext.isDryRun then
                // TODO: Compile module different to Program, fjg 22.01.19
                let isProgram = Option.isSome package.entryPoint
                
                if isProgram then
                    Logging.log6 "Main" ("source code\n")
                    for c in compilations do
                        let codetxt = PPrint.PPrint.render (Some 160) c.implementation
                        let msg = sprintf "Code for %s:\n%s\n" c.name.basicId codetxt
                        Logging.log6 "Main" msg

                    Logging.log2 "Main" ("writing C code for " + inputFile)
                    let ep = package.entryPoint |> Option.get
                
                    // translate module, i.e. compilations
                    // TODO: Additionally take package into account, fjg 10.01.19
                    let codeFile = Path.Combine(cliContext.outDir, SearchPath.moduleToCFile moduleName)
                    let code = CodeGeneration.emitCode translationContext package compilations ep.name
                    FileInfo(codeFile).Directory.Create()
                    File.WriteAllText(codeFile, code)
                
                    // put all types and function prototypes in .h file
                    // TODO: Add exposed subprograms and constants to header, fjg 21.01.19
                    // TODO: Take package into account, fjg 10.01.19
                    let headerFile = Path.Combine(cliContext.outDir, SearchPath.moduleToHFile moduleName)
                    let header = CodeGeneration.emitHeader translationContext package compilations ep.name
                    FileInfo(headerFile).Directory.Create()
                    File.WriteAllText(headerFile, header)

                    // generated test app
                    let appFile = Path.Combine(cliContext.outDir, SearchPath.appNameToCFile cliContext.appName)
                    let app = CodeGeneration.emitApp cliContext package compilations ep.name
                    FileInfo(appFile).Directory.Create()
                    File.WriteAllText(appFile, app)
            
                else 
                    match astAndEnvRes with
                    | Ok (package, lut) ->
                        // Currently we do not compile modules, just create suitable signatures
                        let signatureFile = Path.Combine(cliContext.outDir, SearchPath.moduleToInterfaceFile moduleName)
                        let blechSignature = SignaturePrinter.printSignature lut package
                        FileInfo(signatureFile).Directory.Create()
                        File.WriteAllText(signatureFile, blechSignature)
                    | Error _ ->
                        failwith "this cannot happen"


            // return interface information for module
            tyAstAndLutRes

    // compiledModule is needed for finding the entry point
    //let generateApp (cliContext: Arguments.BlechCOptions) (compiledModule: Package.Module<TypeChecking.TypeCheckContext * BlechTypes.BlechModule>) =  
    //    if not cliContext.isDryRun then
    //        let appFile = Path.Combine(cliContext.outDir, SearchPath.appNameToCFile cliContext.appName)
    //        let dummyPkg = snd compiledModule.info
    //        let app = CodeGeneration.emitApp cliContext dummyPkg
    //        FileInfo(appFile).Directory.Create()
    //        File.WriteAllText(appFile, app)
    //    Ok ()

    let loader options logger packageContext what moduleName infile : Result<Package.Module<TypeCheckContext * BlechTypes.BlechModule>, Diagnostics.Logger> =
        let compilationRes = 
            match what with
            | Package.Implementation ->
                compileImplementation options packageContext logger what moduleName infile
            | Package.Interface ->
                compileInterface options packageContext logger what moduleName infile
                
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
                let cl = CmdLine.handleCommandLine options
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
