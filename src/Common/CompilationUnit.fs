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
    open System.IO

    type CompilationUnitError = 
        | FileNotFound of fileName: string
        | ModuleNotFound of moduleName: FromPath.ModuleName * triedFiles: string list
        | FileNotInSourcePath of inputFileName: string * searchDirs: string list  // TODO: rethink this error messages in the light of modules and packages fjg. 21.09.20
        | IllegalModuleFileName of moduleFileName: string * wrongIds: string list
        | InvalidFileExtension of fileName: string
        
        interface Diagnostics.IDiagnosable with
            
            member err.MainInformation =
                match err with
                | FileNotFound fileName ->
                    { range = Range.rangeCmdArgs
                      message = sprintf "file '%s' not found" fileName}
                | ModuleNotFound (moduleName = mn)->
                    { range = Range.rangeCmdArgs
                      message = sprintf "module '%s' not found" <| SearchPath.moduleNameToString mn }
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
                      sprintf "use '%s' for implementation files." <| SearchPath.implementationFileExtension
                      sprintf "use '%s' for interface files." <| SearchPath.interfaceFileExtension ]

    type ImplOrIface =
        | Implementation
        | Interface

    
    let loadWhat (file: string) =
        if SearchPath.isImplementation file then
            Some Implementation
        elif SearchPath.isInterface file then
            Some Interface
        else
            None


    type Module<'info> = 
        {
            moduleName: FromPath.ModuleName
            file: string
            info: 'info
        }
        static member Make moduleName file info =
            Ok { moduleName = moduleName 
                 file = file 
                 info = info }

        //static member Empty

    type Context<'info> =
        {
            sourcePath: string
            blechPath: string
            package: string  // the name of the package we currently compile, TODO: should be set from the commandline -pkg "mylib", fjg. 22.9.20   
            outDir: string
            logger: Diagnostics.Logger
            loader: Context<'info> -> ImplOrIface -> FromPath.ModuleName -> string -> Result<Module<'info>, Diagnostics.Logger>  
                    // package context -> LoadWhat -> module name -> file name -> Package or logged errors
            loaded: Dictionary<FromPath.ModuleName, Result<Module<'info>, Diagnostics.Logger>>              
                    // module name |-> Package
        }
        static member Make (arguments: Arguments.BlechCOptions) logger loader =
            { sourcePath = arguments.sourcePath
              blechPath = arguments.blechPath
              package = FromPath.ReservedPkg // the default package name is "blech", when nothing is given
              outDir = arguments.outDir
              logger = logger
              loader = loader
              loaded = Dictionary<FromPath.ModuleName, Result<Module<'info>, Diagnostics.Logger>>() }

    
    /// loads a program or or a module for compilation
    let load (ctx: Context<'info>) (fileName: string) =
          
        let lgr = ctx.logger
        let optLw = loadWhat fileName
        
        if Option.isNone optLw then
            Diagnostics.Logger.logFatalError 
            <| lgr
            <| Diagnostics.Phase.Compiling
            <| InvalidFileExtension fileName 
            Error lgr
        elif not (SearchPath.canOpen fileName) then
            Diagnostics.Logger.logFatalError 
            <| lgr
            <| Diagnostics.Phase.Compiling
            <| FileNotFound fileName 
            Error lgr
        else 
            let loadWhat = Option.get optLw 
            match SearchPath.getModuleName ctx.sourcePath None fileName with
            | Error [] ->
                Diagnostics.Logger.logFatalError 
                <| lgr
                <| Diagnostics.Phase.Compiling
                <| FileNotInSourcePath (fileName, SearchPath.searchPath2Dirs ctx.sourcePath)
                Error lgr
            | Error wrongIds ->
                Diagnostics.Logger.logFatalError 
                <| lgr
                <| Diagnostics.Phase.Compiling
                <| IllegalModuleFileName (fileName, wrongIds)
                Error lgr
            | Ok moduleName ->
                // TODO: check if file is already compiled
                ctx.loader ctx loadWhat moduleName fileName


    /// requires an imported module for compilation
    let require (ctx: Context<'info>) (moduleName: FromPath.ModuleName): Result<Module<'info>, Diagnostics.Logger> =
        
        let tryBlechPath triedBlcs =
            let sigFile = SearchPath.searchInterface ctx.blechPath moduleName 
            match sigFile with
            | Ok blh ->
                ctx.loader ctx Interface moduleName blh
            | Error triedBlhs ->
                let lgr = ctx.logger
                Diagnostics.Logger.logFatalError 
                <| lgr
                <| Diagnostics.Phase.Compiling
                <| ModuleNotFound (moduleName, triedBlcs @ triedBlhs) 
                Error lgr

        if ctx.loaded.ContainsKey moduleName then
            ctx.loaded.[moduleName]
        else
            let blcFile = SearchPath.searchImplementation ctx.sourcePath moduleName
            let blhFile = SearchPath.searchInterface ctx.outDir moduleName
            match blhFile, blcFile with
            | Ok blh, Ok blc ->
                // TODO: compare blh and blc, if valid blh exists compile the blh as 'Interface' else
                let compiled = ctx.loader ctx Implementation moduleName blc
                ctx.loaded.Add (moduleName, compiled)
                compiled
                // TODO: here we need to call the complete compilation procedure
                
            | Error _, Ok blc ->
                ctx.loader ctx Implementation moduleName blc
            
            | _ , Error triedBlcs ->
                tryBlechPath triedBlcs
            