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


    let private runNameResolution logger moduleName inputFile importedEnvs ast =
        Logging.log2 "Main" ("performing name resolution on " + inputFile)
        NameChecking.initialise logger moduleName importedEnvs
        |> NameChecking.checkDeclaredness <| ast


    let private runTypeChecking cliArgs logger inputFile otherLuts astAndEnv =
        Logging.log2 "Main" ("performing type checking on " + inputFile)
        TypeChecking.typeCheck cliArgs logger otherLuts astAndEnv


    let private runCausalityCheck logger inputFile tyAstAndLut =
        Logging.log2 "Main" ("checking causality in " + inputFile) 
        Causality.checkPackCausality logger tyAstAndLut

        
    //---
    //  Functions that write to the file system during compilation
    //---

    let private writeFile outFileName txt =
        FileInfo(outFileName).Directory.Create()
        do File.WriteAllText(outFileName, txt)


    let private writeSignature outDir moduleName ncEnv ast =
        let signatureFile = Path.Combine(outDir, TranslatePath.moduleToInterfaceFile moduleName)
        let blechSignature = SignaturePrinter.printSignature ncEnv ast
        do writeFile signatureFile blechSignature


    let private writeImplementation outDir moduleName (blechModule: BlechTypes.BlechModule) otherMods translationContext compilations =
        let codeFile = Path.Combine(outDir, TranslatePath.moduleToCFile moduleName)
        let code = 
            match blechModule.entryPoint with
            | Some ep ->
                CodeGeneration.emitMainCode translationContext blechModule compilations ep.name
            | None ->
                CodeGeneration.emitCode translationContext blechModule compilations
        do writeFile codeFile code


    let private writeHeader outDir moduleName (blechModule: BlechTypes.BlechModule) otherMods translationContext compilations =
        let headerFile = Path.Combine(outDir, TranslatePath.moduleToHFile moduleName)
        let header = 
            match blechModule.entryPoint with
            | Some ep ->
                CodeGeneration.emitMainHeader translationContext blechModule otherMods compilations ep.name
            | None ->
                CodeGeneration.emitHeader translationContext blechModule otherMods compilations
        do writeFile headerFile header


    let private possiblyWriteTestApp (cliArgs: Arguments.BlechCOptions) (blechModule: BlechTypes.BlechModule) translationContext compilations =
        match cliArgs.appName, blechModule.entryPoint with
        | Some an, Some ep ->
            let appFile = Path.Combine(cliArgs.outDir, TranslatePath.appNameToCFile an)
            let app = CodeGeneration.emitApp translationContext blechModule compilations ep.name
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

    type private ModuleInfo = ImportChecking.ModuleInfo
    type private Imports = ImportChecking.Imports

    let compileFromStr cliArgs (pkgCtx: CompilationUnit.Context<ModuleInfo>) logger moduleName fileName fileContents =
        // always run lexer, parser, name resolution, type check and causality checks
        
        let astRes = runParser logger CompilationUnit.Implementation moduleName fileContents fileName
        
        let imports =  // TODO: Result.bind this to a successful AST result, fjg. 23.10.20  
            if Result.isOk astRes then
                let ast = Result.getOk astRes
                ImportChecking.checkImports pkgCtx logger ast
            else
                Imports.Empty
            
        // TODO: run compilation of imports here. Here you need the current from-path from the parameter list, 
        // to determine the frompath of a relative import (FromPath.makeFromPath) instead of the modulename
        // fjg. 24.09.20

        //let imports = astRes |> Result.map (fun p -> p.imports |> List.filter (fun (m: AST.Member) -> not m.IsAPragma))
        //let importedModules = 
        //    imports 
        //    |> function
        //        | Ok imports -> imports |> (List.map (checkImport pkgCtx fromPath))
        //        | Error lgr -> [Error lgr]

        //let contractCompUnits cuLst =
        //    let rec recContract cus res =
        //        match cus with
        //        | [] -> res
        //        | x::xs ->
        //            match x, res with
        //            | Error e1, _ -> recContract xs <| Error e1 // TODO: merge Diagnostics!
        //            | _, Error errs -> recContract xs <| Error errs
        //            | Ok sth, Ok someList -> recContract xs (Ok (someList @ [sth])) // respect the order!
        //    recContract cuLst (Ok [])

        //let fst4 (a, _, _, _) = a
        //let snd4 (_, a, _, _) = a
        //let trd4 (_, _, a, _) = a
        //let frt4 (_, _, _, a) = a

        // get all top-level scopes of precompiled modules
        // add them to the top level scope of the current compilation unit
        // TODO: prefix with the given import name!
        //let insertLocalName (ln: CommonTypes.Name) (env: SymbolTable.Environment) = //(path: SymbolTable.Scope list) =
        //    match env.path with
        //    | [] -> env //[]
        //    | globalScope :: tail ->
        //        {env with path = SymbolTable.Scope.rewriteId globalScope ln.id :: tail}                

        //let envsRes = 
        //    importedModules
        //    |> contractCompUnits
        //    |> Result.map (List.map (fun cu -> cu.info))
        //    //|> Result.map (List.map(fun (localName,cu) -> insertLocalName localName 
            //                                                (fst4 cu.info), snd4 cu.info, trd4 cu.info, frt4 cu.info))
            //|> Result.map (List.map (fun (localName,cu) -> cu.info))
            //|> Result.map (List.concat)

        // addModule ctx p.moduleName  // TODO: use this just for imports
        // TODO: checkModuleName for shadowing of imports
        //match envsRes with
        //| Error foo -> Error foo
        //| Ok cus ->
        //    //  let envs, otherLuts, otherMods, preTranslationContexts = List.unzip4 cus

        let astAndSymTableRes = // TODO: Result.bind this to a successful import check, fjg. 23.10.20
            let importedEnvs = imports.GetNameCheckEnvironments // TODO: Take this from the package Context, fjg. 23.10.20
            astRes 
            |> Result.bind (runNameResolution logger moduleName fileName importedEnvs)
        
        let lutAndPackRes = 
            let otherLuts = imports.GetTypeCheckContexts
            astAndSymTableRes 
            |> Result.bind (fun (ast, env) -> runTypeChecking cliArgs logger fileName otherLuts (ast, env.lookupTable))
        
        let pgsRes = 
            lutAndPackRes 
            |> Result.bind (runCausalityCheck logger fileName)
            
        match astAndSymTableRes, lutAndPackRes, pgsRes with    
        | Ok (ast, env), Ok (lut, blechModule), Ok pgs ->
            // generate block graphs for all activities
            // this is only needed for code generation but is left here for debugging purposes
            let blockGraphContext = BlockGraph.bgCtxOfPGs pgs
            let preTranslationContexts = imports.GetTranslationContexts
            let preCompilations = preTranslationContexts |> List.collect (fun ctx -> ctx.compilations)
            let translationContext: TranslationContext =
                { tcc = lut
                  pgs = pgs
                  bgs = blockGraphContext 
                  compilations = preCompilations
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
                    do writeSignature cliArgs.outDir moduleName lut.ncEnv ast

                Logging.log2 "Main" ("writing C code for " + fileName)

                
                let otherMods = imports.GetTypedModules
                // TODO: Add otherMods to writeImplementation
                // implementation should also include headers of imported modules, fjg. 19.10.20
                do writeImplementation cliArgs.outDir moduleName blechModule otherMods translationContext compilations
                do writeHeader cliArgs.outDir moduleName blechModule otherMods translationContext compilations
                // generated test app if required by cliArgs
                do possiblyWriteTestApp cliArgs blechModule translationContext compilations

            // return interface information and dependencies for module 
            let importedModules = imports.GetImportedModules
            Ok <| ImportChecking.ModuleInfo.Make importedModules env lut blechModule translationContext

        | _ ->
            // let errorImports = imports.GetErrorImports
            Error <| logger

                
    /// Runs compilation starting with a filename
    let compileFromFile cliArgs pkgCtx logger moduleName inputFile =
        // open stream from file
        File.ReadAllText (Path.GetFullPath(inputFile))
        |> compileFromStr cliArgs pkgCtx logger moduleName inputFile
    

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

        
    let loader options packageContext logger implOrIface moduleName infile 
            : Result<CompilationUnit.Module<ImportChecking.ModuleInfo>, Diagnostics.Logger> =
        let compilationRes = 
            match implOrIface with
            | CompilationUnit.Implementation ->
                compileFromFile options packageContext logger moduleName infile
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
            CompilationUnit.load pkgCtx logger inputFile
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
