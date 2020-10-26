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

namespace Blech.Common

[<RequireQualifiedAccess>]
module CompilationUnit =
    
    open System.Collections.Generic
    
    open TranslationUnitPath


    type CompilationUnitError = 
        | FileNotFound of fileName: string
        | ModuleNotFound of moduleName: TranslationUnitPath * range: Range.range * triedFiles: string list
        | FileNotInSourcePath of inputFileName: string * searchDirs: string list  // TODO: rethink this error messages in the light of modules and packages fjg. 21.09.20
        | IllegalModuleFileName of moduleFileName: string * wrongIds: string list
        | InvalidFileExtension of fileName: string
        
        interface Diagnostics.IDiagnosable with
            
            member err.MainInformation =
                match err with
                | FileNotFound fileName ->
                    { range = Range.rangeCmdArgs
                      message = sprintf "file '%s' not found" fileName}
                | ModuleNotFound (moduleName = mn; range = rng)->
                    { range = rng
                      message = sprintf "module '%s' not found" <| mn.ToString() }
                | FileNotInSourcePath (inputFileName = ifn) ->
                    { range = Range.rangeCmdArgs
                      message = sprintf "input file '%s' outside source path" ifn}
                | IllegalModuleFileName (moduleFileName = mfn) ->
                    { range = Range.rangeCmdArgs
                      message = sprintf "module file '%s' is not a valid blech file name" mfn}
                | InvalidFileExtension fileName ->
                    { range = Range.rangeCmdArgs
                      message = sprintf "file '%s' uses and invalid Blech file extension" fileName}
                
           
            member err.ContextInformation = 
                match err with
                | ModuleNotFound (range = rng) ->
                    [ { range = rng; message = "not found"; isPrimary = true } ]
                | _ -> 
                    []
            
            member err.NoteInformation =
                match err with 
                | FileNotFound fileName ->
                    []
                | ModuleNotFound (triedFiles = fs) ->
                    List.map (fun f -> sprintf "no file '%s'" f) fs
                | FileNotInSourcePath (_, searchDirs) ->
                    List.map (fun sd -> sprintf "not in '%s'" sd) searchDirs
                | IllegalModuleFileName (wrongIds = wids) ->
                    List.map (fun id -> sprintf "wrong id '%s'" id) wids
                | InvalidFileExtension fn ->
                    [ sprintf "invalid file extension '%s'." <| System.IO.Path.GetExtension fn
                      sprintf "use '%s' for implementation files." <| implementationFileExtension
                      sprintf "use '%s' for interface files." <| interfaceFileExtension ]

    
    type ImplOrIface =
        | Implementation
        | Interface

    
    let loadWhat (file: string) =
        if isImplementation file then
            Some Implementation
        elif isInterface file then
            Some Interface
        else
            None



    type ImportChain =
        private { chain : TranslationUnitPath list } // in reverse order
                
        static member Empty = 
            { chain = [] }
        
        member this.Increase moduleName =
            { chain = moduleName :: this.chain }

        member this.Decrease =
            { chain = List.tail this.chain}

        member this.Contains moduleName =  // detects a cyclic import
            List.contains moduleName this.chain
 
 

    type Module<'info> = 
        {
            moduleName: TranslationUnitPath
            file: string
            info: 'info
        }
        static member Make (fromPath : TranslationUnitPath) file info =
            Ok { moduleName = fromPath
                 file = file 
                 info = info }


    type Context<'info> =
        {
            sourcePath: string
            blechPath: string
            package: string option // the name of the package we currently compile, TODO: should be set from the commandline -pkg "mylib", fjg. 22.9.20   
            outDir: string
            // logger: Diagnostics.Logger
            loader: Context<'info> -> Diagnostics.Logger -> ImportChain -> ImplOrIface -> TranslationUnitPath -> string -> Result<Module<'info>, Diagnostics.Logger>  
                    // package context -> module logger -> import chain -> LoadWhat -> from path -> file name -> Package or logged errors
            loaded: Dictionary<TranslationUnitPath, Result<Module<'info>, Diagnostics.Logger>>              
                    // module name |-> Package
        }
        static member Make (arguments: Arguments.BlechCOptions) loader =
            { sourcePath = arguments.sourcePath
              blechPath = arguments.blechPath
              package = None //PathRegex.ReservedPkg // the default package name is "blech", when nothing is given
              outDir = arguments.outDir
              // logger = logger
              loader = loader
              loaded = Dictionary<TranslationUnitPath, Result<Module<'info>, Diagnostics.Logger>>() }

        member this.GetErrorImports : (TranslationUnitPath * Diagnostics.Logger) list =
            [ for pairs in this.loaded do 
                if Result.isError pairs.Value then yield pairs.Key, Result.getError pairs.Value ]

        member this.GetOkImports : Dictionary<TranslationUnitPath, Module<'info>> =
            let oks = Dictionary()
            for pairs in this.loaded do 
                if Result.isOk pairs.Value then 
                    oks.Add (pairs.Key, Result.getOk pairs.Value)
            oks
                    
       
        member this.GetLoaded =
            Seq.toList (this.loaded.Values)
            
        
    /// loads a program or or a module for compilation
    /// Given a context with package information and a filename
    /// try to determine a TranslationUnitName for it and load it
    let load (ctx: Context<'info>) logger importChain (fileName: string)
            : Result<Module<'info>, Diagnostics.Logger> =
        // let logger = ctx.logger
        let optLw = loadWhat fileName
        
        // file exists and is readable?
        if not (canOpen fileName) then
            Diagnostics.Logger.logFatalError 
            <| logger
            <| Diagnostics.Phase.Compiling
            <| FileNotFound fileName 
            Error logger
        else
            // file belongs to the source directory?
            match tryFindSourceDir fileName ctx.sourcePath with
            | None ->
                Diagnostics.Logger.logFatalError 
                <| logger
                <| Diagnostics.Phase.Compiling
                <| FileNotInSourcePath (fileName, searchPath2Dirs ctx.sourcePath)
                Error logger
            | Some srcDir ->
                // file is either .blc or .blh?
                match optLw with
                | None ->
                    Diagnostics.Logger.logFatalError 
                    <| logger
                    <| Diagnostics.Phase.Compiling
                    <| InvalidFileExtension fileName 
                    Error logger
                | Some loadWhat ->
                    // file and source directory have valid names?
                    match tryMakeTranslationUnitPath fileName srcDir ctx.package with
                    | Error wrongIds ->
                        Diagnostics.Logger.logFatalError 
                        <| logger
                        <| Diagnostics.Phase.Compiling
                        <| IllegalModuleFileName (fileName, wrongIds)
                        Error logger
                    | Ok translationUnitPath ->
                        // a valid TranslationUnitPath has been constructed
                        // now load it
                        // TODO: check if file is already compiled
                        ctx.loader ctx logger importChain loadWhat translationUnitPath fileName


    /// requires an imported module for compilation
    /// Given a context (including loaded translation units) and the 
    /// TranslationUnitPath to a translation unit to be loaded
    /// load the unit, compile it and return the compilation result for imported usage

    let require (ctx: Context<'info>) logger importChain (requiredModule: TranslationUnitPath) (importRange: Range.range)
            : Result<Module<'info>, Diagnostics.Logger> =
        if ctx.loaded.ContainsKey requiredModule then
            ctx.loaded.[requiredModule]
        else
            let compiled = 
                let blcFile = searchImplementation ctx.sourcePath requiredModule
                let blhFile = searchInterface ctx.outDir requiredModule
                match blhFile, blcFile with
                | Ok blh, Ok blc ->
                    // TODO: compare blh and blc, if valid blh exists compile the blh as 'Interface' else
                    ctx.loader ctx logger importChain Implementation requiredModule blc
                    //let compiled = ctx.loader ctx freshLogger Implementation requiredModule blc
                    //ctx.loaded.Add (requiredModule, compiled)
                    //compiled
                | Error _, Ok blc ->
                    ctx.loader ctx logger importChain Implementation requiredModule blc
                    //let compiled = ctx.loader ctx freshLogger Implementation requiredModule blc
                    //ctx.loaded.Add (requiredModule, compiled)
                    //compiled
                | _ , Error triedBlcs ->
                    let sigFile = searchInterface ctx.blechPath requiredModule 
                    match sigFile with
                    | Ok blh ->
                        // ctx.loader ctx freshLogger Interface requiredModule blh
                        ctx.loader ctx logger  importChain Implementation requiredModule blh
                        //let compiled = ctx.loader ctx freshLogger Implementation requiredModule blh
                        //ctx.loaded.Add (requiredModule, compiled)
                        //compiled
                    | Error triedBlhs ->
                        // let lgr = ctx.logger
                        printfn "Module not found: %s" <| requiredModule.ToString()
                        Diagnostics.Logger.logFatalError 
                        <| logger
                        <| Diagnostics.Phase.Compiling
                        <| ModuleNotFound (requiredModule, importRange, triedBlcs @ triedBlhs) 
                        Error logger
            
            ctx.loaded.Add (requiredModule, compiled)
            compiled
