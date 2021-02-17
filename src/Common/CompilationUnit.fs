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
                
           
            member err.ContextInformation = []
            
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

    
    

    type ImportChain =
        private { chain : TranslationUnitPath list } // in reverse order
                
        static member Empty = 
            { chain = [] }
        
        member this.Extend moduleName =
            { chain = moduleName :: this.chain }

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


    type TranslatedUnit =
        | Implementation of TranslationUnitPath
        | Interface of TranslationUnitPath


    type ImplOrIface =
        | Blc
        | Blh


    let loadWhat (file: string) =
        if isImplementation file then
            Some Blc
        elif isInterface file then
            Some Blh
        else
            None


    type Context<'info> =
        {
            sourcePath: string
            blechPath: string
            package: string option // the name of the package we currently compile, TODO: should be set from the commandline -pkg "mylib", fjg. 22.9.20   
            outDir: string
            loader: Context<'info> -> Diagnostics.Logger -> ImportChain -> ImplOrIface -> TranslationUnitPath -> string -> Result<Module<'info>, Diagnostics.Logger>  
                    // package context -> module logger -> import chain -> LoadWhat -> module name -> file name -> compiled module or errors in logged errors
            loaded: Dictionary<TranslatedUnit, Result<Module<'info>, Diagnostics.Logger>>              
                    // module name |-> compiled module or errors in logger
        }
        static member Make (arguments: Arguments.BlechCOptions) loader =
            { sourcePath = arguments.sourcePath
              blechPath = arguments.blechPath
              package = None
              outDir = arguments.outDir
              loader = loader
              loaded = Dictionary<TranslatedUnit, Result<Module<'info>, Diagnostics.Logger>>() }

        member this.GetErrorImports : (TranslatedUnit * Diagnostics.Logger) list =
            [ for pairs in this.loaded do 
                if Result.isError pairs.Value then yield pairs.Key, Result.getError pairs.Value ]

        member this.GetOkImports : Dictionary<TranslatedUnit, Module<'info>> =
            let oks = Dictionary()
            for pairs in this.loaded do 
                if Result.isOk pairs.Value then 
                    oks.Add (pairs.Key, Result.getOk pairs.Value)
            oks

        member this.IsLoaded moduleName = 
            this.loaded.ContainsKey <| Implementation moduleName
            || this.loaded.ContainsKey <| Interface moduleName

        member this.GetLoaded =
            Seq.toList (this.loaded.Values)


    /// loads a program or a module for compilation
    /// Given a context with package information, a diagnostic logger for errors, an import chain and a filename
    /// try to determine a TranslationUnitName for it and load it
    let load (ctx: Context<'info>) logger (importChain: ImportChain) (fileName: string)
            : Result<Module<'info>, Diagnostics.Logger> =
        
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
                    | Ok translationUnit ->
                        // a valid TranslationUnitPath has been constructed
                        // now load it
                        // TODO: check if file is already compiled
                        let initialImportChain = importChain.Extend translationUnit
                        ctx.loader ctx logger initialImportChain loadWhat translationUnit fileName
                        

    /// requires an imported module for compilation
    /// Given a context (including loaded translation units) and the 
    /// TranslationUnitPath to a translation unit to be loaded
    /// load the unit, compile it, cache it 
    /// generate the signature, compile it, cache it
    /// and return the compilation result for imported usage
    let require (ctx: Context<'info>) logger importChain (requiredModule: TranslationUnitPath) (importRange: Range.range)
            : Result<Module<'info>, Diagnostics.Logger> =
        let translatedMod = Implementation requiredModule
        let translatedSig = Interface requiredModule
        if ctx.loaded.ContainsKey translatedSig then
            // printfn "Use compiled module: %A" translatedSig
            ctx.loaded.[translatedSig]
        else
            let blcFile = searchImplementation ctx.sourcePath requiredModule
            
            match blcFile with
            | Ok blc ->
                let compiledBlcRes = ctx.loader ctx logger importChain Blc requiredModule blc
                do ctx.loaded.Add (translatedMod, compiledBlcRes)

                // if Result.isOk compiledBlcRes then 
                match compiledBlcRes with 
                | Ok moduleInfo -> 
                    let blhFile = searchInterface ctx.sourcePath requiredModule // TODO: Simplify this, if possible
                    match blhFile with
                    | Ok blh -> 
                        // signature found
                        let compiledBlhRes = ctx.loader ctx logger importChain Blh requiredModule blh
                        do ctx.loaded.Add (translatedSig, compiledBlhRes)
                        compiledBlhRes           
                    | Error _ ->
                        // no generated signature implies .blc must be a program
                        // TODO: This is a dangerous conclusion if .blh is missing due to other reasons
                        // TODO: Make this safer, fjg 16.02.21
                        Ok moduleInfo
                | Error reqLgr ->
                    Error reqLgr // logger of required module
            
            | Error triedBlcs ->
                do Diagnostics.Logger.logFatalError logger Diagnostics.Phase.Compiling
                    <| ModuleNotFound (requiredModule, importRange, triedBlcs) 
                do ctx.loaded.Add(translatedMod, Error logger) // errors must be cached, too
                Error logger // logger of importing module 

