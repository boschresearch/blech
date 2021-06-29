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
module Arguments =
    
    open Argu // see: https://fsprojects.github.io/Argu/index.html
    open System.IO

    type Verbosity = 
        | Q 
        | Quiet
        | M
        | Minimal
        | N
        | Normal
        | D
        | Detailed
        | Diag
        | Diagnostic

 
    //type Trace = 
    //    | Json
    //    | Xml
    //    | Csv
    
    let defaultBlechPath = "."
    let defaultProjectDir = "." 
    let defaultOutDir = Path.Combine (".", "blech") // put all generated files into blech folder bei default
    let defaultAppName = "blech"
    
    
    type BlechCArg =
        | Version
        | Rebuild 
        | Dry_Run
        | [<Unique; AltCommandLine("-v")>] Verbosity of level : Verbosity 
        
        | [<Unique; EqualsAssignment>] App of name : string option
        | [<Unique; AltCommandLine("-pd")>] Project_Dir of directory : string 
        | [<Unique; AltCommandLine("-od")>] Out_Dir of directory : string
        | [<Unique; AltCommandLine("-bp")>] Blech_Path of path : string
        
        | [<Unique; EqualsAssignment>] Box of name : string
        // code generation configuration
        | [<Unique; EqualsAssignment>] Word_Size of bits: int
        | [<Unique>] Trace
        | [<Unique>] Pass_Primitive_By_Address
        
        // input is only one file, because of the module system
        | [<Last; Unique; MainCommand>] Input of filename : string
        
        interface IArgParserTemplate with
            member args.Usage =
                match args with
                | Version ->
                    "show version information."
                | Rebuild -> 
                    "always re-compile from source files."
                | Dry_Run _ -> 
                    "do not generate any C code files."
                | Verbosity _ -> 
                    "set verbosity <level>, "
                    + "allowed values are q[uiet], m[inimal], n[ormal], d[etailed], diag[nostic]."
                
                | App _ -> 
                    "generate '<name>.c' as main application, default is '" + defaultAppName + ".c'."
                | Project_Dir _ ->
                    "search for blech modules in <directory>, "
                    + "defaults to " + "\"" + defaultProjectDir + "\"" + "."
                | Out_Dir _ -> 
                    "write all build results to <directory>, which must already exist."
                | Blech_Path _ ->
                    "search for blech library modules in <path>, "
                    + "defaults to " + "\"" + defaultBlechPath + "\"" + "."
                
                | Box _ ->
                    "compile for box <name>, allowed names are valid Blech identifiers."
                
                | Word_Size _ -> 
                    "maximum word size, "
                    + "allowed values are 8, 16, 32, 64."
                | Trace -> 
                    "generate traces on stdout."
                | Pass_Primitive_By_Address ->
                    "pass Blech input arguments of primitive type by address."
                | Input _ -> 
                    "file <name> to be compiled."


    type WordSize = 
        | W8 | W16 | W32 | W64

        member this.ToInt : int =
            match this with
            | W8 -> 8
            | W16 -> 16
            | W32 -> 32
            | W64 -> 64
            
        static member FromInt wordsize = 
            match wordsize with
            | 8 -> W8
            | 16 -> W16
            | 32 -> W32
            | 64 -> W64
            | _ -> failwith <| "invalid word size " + string wordsize + "."
               
    type BlechCOptions =  // TODO: Move this to separate file in utils
        {
            inputFile: string
            box: string option
            appName: string option
            projectDir : string
            outDir: string
            blechPath: string
            showVersion: bool
            isDryRun: bool
            isRebuild: bool
            isFrontendTest : bool // used to stop import compilation before type check
            trace: bool
            wordSize: WordSize
            passPrimitiveByAddress: bool
            verbosity: Verbosity
        }

        static member Default = {
                inputFile = ""
                box = None
                appName = None
                projectDir = defaultProjectDir 
                outDir = defaultOutDir
                blechPath = defaultBlechPath
                showVersion = false
                isDryRun = false
                isRebuild = false
                isFrontendTest = false // currently used to test language features that do not typecheck
                trace = false
                wordSize = W32
                passPrimitiveByAddress = false
                verbosity = Quiet
            }

        
    let private changeOptionFromArg (opts: BlechCOptions) (arg: BlechCArg) : BlechCOptions =
        match arg with
        | Version ->
            { opts with showVersion = true }
        | Input fn ->
            { opts with inputFile = fn}
        | App an ->
            match an with
            | Some _ -> 
                { opts with appName = an }
            | None ->
                { opts with appName = Some defaultAppName }
        | Rebuild ->
            { opts with isRebuild = true }
        | Dry_Run ->
            { opts with isDryRun = true }
        | Project_Dir pd ->
            { opts with projectDir = pd }
        | Out_Dir od ->
            { opts with outDir = od }
        | Blech_Path bp ->
            { opts with blechPath = bp}
        | Box bn ->
            { opts with box = Some bn}
        | Verbosity v ->
            { opts with verbosity = v }
        | Word_Size ws ->
            { opts with wordSize = WordSize.FromInt ws }
        | Trace ->
            { opts with trace = true }
        | Pass_Primitive_By_Address ->
            { opts with passPrimitiveByAddress = true }


    let private parseWordSize ws = 
        if ws = 8 || ws = 16 || ws = 32 || ws = 64 then
            ws
        else
            failwith <| "invalid word size " + string ws + ". Allowed values are 8, 16, 32, 64."

    let private parseBoxName bn = 
        if TranslationUnitPath.PathRegex.isValidFileOrDirectoryName bn then
            bn
        else
            failwith <| sprintf "invalid library name \"%s\". Allowed names are valid Blech identifiers." bn

    let parser = 
        ArgumentParser.Create<BlechCArg>(programName = "blechc")
    
    type CommandLineHelp = string

    let collectOptions (argv : string[]) : Result<BlechCOptions, CommandLineHelp> =
        try
            let config = parser.ParseCommandLine(inputs = argv, raiseOnUsage = true)
    
            if config.Contains <@ Word_Size @> then 
                ignore <| config.PostProcessResult(<@ Word_Size @>, parseWordSize)
            if config.Contains <@ Box @> then
                ignore <| config.PostProcessResult(<@ Box @>, parseBoxName)
    
            let opts =
                config.GetAllResults()
                |> List.fold changeOptionFromArg BlechCOptions.Default
            
            Ok opts 
        with e ->
            Error e.Message