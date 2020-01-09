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

module CmdLine =

    open System.IO
    open Blech.Common


    type CommandLineError = 
        | NoInputModule
        | NoOutDir of directory: string
        
        interface Diagnostics.IDiagnosable with
            
            member err.MainInformation =
                match err with
                | NoInputModule -> 
                    { range = Range.rangeCmdArgs
                      message = "no input module given" }

                | NoOutDir directory ->
                    { range = Range.rangeCmdArgs
                      message = sprintf "output directory '%s' not found" directory }
           
            member err.ContextInformation = []
            
            member err.NoteInformation =
                match err with 
                | NoInputModule ->
                    [ "see 'blechc --help'" ]
                | NoOutDir _ ->
                    [ "make sure output directory exists and has read/write access"]


    type Action =
        | ShowVersion
        | Compile


    let handleCommandLine (options: Arguments.BlechCOptions) : Result<Action, Diagnostics.Logger> =
        
        Logging.setLogLevel options.verbosity
        if options.showVersion then 
            Ok ShowVersion
        else
            let logger = Diagnostics.Logger.create()  
            if options.inputFile = "" then 
                (logger, Diagnostics.Phase.Compiling) ||> Diagnostics.Logger.logFatalError <|  NoInputModule
        
            if not (Directory.Exists options.outDir || options.isDryRun ) then
                (logger, Diagnostics.Phase.Compiling) ||> Diagnostics.Logger.logFatalError <| NoOutDir options.outDir
    
            if Diagnostics.Logger.hasErrors logger then
                Error logger
            
            else
                Ok Compile
 


