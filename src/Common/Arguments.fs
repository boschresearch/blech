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
    let defaultSourcePath = "." 
    let defaultOutDir = "."
    let defaultAppName = "blech"
    
    
    type BlechCArg =
        | Version
        | Rebuild 
        | Dry_Run
        | [<Unique; AltCommandLine("-v")>] Verbosity of level : Verbosity 
        
        | [<Unique; EqualsAssignment>] App of name : string option
        | [<Unique; AltCommandLine("-sp")>] Source_Path of path : string 
        | [<Unique; AltCommandLine("-od")>] Out_Dir of directory : string
        | [<Unique; AltCommandLine("-bp")>] Blech_Path of path : string
        
        // code generation configuration
        | [<Unique; EqualsAssignment>] Word_Size of bits: int
        | [<Unique>] Trace
        | [<Unique; AltCommandLine("-vis")>] Visualize
        | [<Unique; AltCommandLine("-vis_breakRunStmt")>] Vis_BreakRunStatement
        | [<Unique; AltCommandLine("-vis_cbgnPatternWithHier")>] Vis_CbgnPatternWithHier
        | [<Unique; AltCommandLine("-vis_NoCbgnPattern")>] Vis_NoCbgnPattern
        | [<Unique; AltCommandLine("-vis_includeOrigcode")>] Vis_includeOrigCode
        | [<Unique; AltCommandLine("-vis_notUseConnector")>] Vis_notUseConnector
        | [<Unique; AltCommandLine("-vis_disableBreakHier")>] Vis_DisableBreakHier
        | [<Unique; AltCommandLine("-vis_disableCollapseTrans")>] Vis_DisableCollapseTrans
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
                    "do not write any result files."
                | App _ -> 
                    "generate '<name>.c' as main application, default is '" + defaultAppName + ".c'."
                | Source_Path _ ->
                    "search for blech modules in <path> templates, "
                    + "defaults to " + "\"" + defaultSourcePath + "\"" + "."
                | Out_Dir _ -> 
                    "write all build results to <directory>, which must already exist."
                | Blech_Path _ ->
                    "search for blech modules in <path> templates, "
                    + "defaults to " + "\"" + defaultBlechPath + "\"" + "."
                | Verbosity _ -> 
                    "set verbosity <level>, "
                    + "allowed values are q[uiet], m[inimal], n[ormal], d[etailed], diag[nostic]."
                | Word_Size _ -> 
                    "maximum word size, "
                    + "allowed values are 8, 16, 32, 64."
                | Trace -> 
                    "generate traces on stdout."
                | Pass_Primitive_By_Address ->
                    "pass Blech input arguments of primitive type by address."
                | Input _ -> 
                    "file <name> to be compiled."
                | Visualize _ ->
                    "outputs a .sctx file in the current directory that visualizes an abstract (stateful) view of the code in the given file."
                | Vis_BreakRunStatement _ ->
                    "indicates, whether a generated abstract visualization of the code should break the hierarchies on run statements."
                | Vis_CbgnPatternWithHier _ ->
                    "alternative improvement of cobegin pattern. Instead of breaking the hierarchy, a hierarchical node with weak abort transition is added."
                | Vis_NoCbgnPattern _ ->
                    "turns off the cobegin pattern detection in the visualization."
                | Vis_includeOrigCode _ ->
                    "if this flag is set, the original BlechCode is included as a comment in the resulting .sctx."
                | Vis_notUseConnector _ ->
                    "if used, connector states are not used."
                | Vis_DisableBreakHier _ ->
                    "Disables the simplification step of breaking hierarchies. Not recommended."
                | Vis_DisableCollapseTrans _ ->
                    "Disables the simplification step of collapsing transient transitions. Not recommended."

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
            appName: string option
            sourcePath: string
            outDir: string
            blechPath: string
            showVersion: bool
            isDryRun: bool
            isRebuild: bool
            trace: bool
            wordSize: WordSize
            passPrimitiveByAddress: bool
            verbosity: Verbosity
            visualize: bool
            vis_breakHierOnActCalls: bool
            vis_cbgnPatternWithHier : bool
            vis_noCbgnPattern : bool
            vis_includeOrigCode : bool
            vis_notUseConnector : bool
            vis_disableBreakHier : bool 
            vis_disableCollapseTrans : bool
        }
        static member Default = {
                inputFile = ""
                appName = None
                sourcePath = defaultSourcePath
                outDir = defaultOutDir
                blechPath = defaultBlechPath
                showVersion = false
                isDryRun = false
                isRebuild = false
                trace = false
                wordSize = W32
                passPrimitiveByAddress = false
                verbosity = Quiet
                visualize = false
                vis_breakHierOnActCalls = false
                vis_cbgnPatternWithHier = false
                vis_noCbgnPattern = false
                vis_includeOrigCode = false
                vis_notUseConnector = false
                vis_disableBreakHier = false
                vis_disableCollapseTrans = false
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
        | Source_Path sp ->
            { opts with sourcePath = sp }
        | Out_Dir od ->
            { opts with outDir = od }
        | Blech_Path bp ->
            { opts with blechPath = bp}
        | Verbosity v ->
            { opts with verbosity = v }
        | Word_Size ws ->
            { opts with wordSize = WordSize.FromInt ws }
        | Trace ->
            { opts with trace = true }
        | Pass_Primitive_By_Address ->
            { opts with passPrimitiveByAddress = true }
        | Visualize _ ->
            { opts with visualize = true }
        | Vis_BreakRunStatement _ ->
            { opts with vis_breakHierOnActCalls = true }
        | Vis_CbgnPatternWithHier _ ->
            { opts with vis_cbgnPatternWithHier = true }
        | Vis_NoCbgnPattern _ ->
            { opts with vis_noCbgnPattern = true }
        | Vis_includeOrigCode _ ->
            { opts with vis_includeOrigCode = true }
        | Vis_notUseConnector _ ->
            { opts with vis_notUseConnector = true }
        | Vis_DisableBreakHier _ ->
            { opts with vis_disableBreakHier = true }
        | Vis_DisableCollapseTrans _ ->
            { opts with vis_disableCollapseTrans = true }

    let private parseWordSize ws = 
        if ws = 8 || ws = 16 || ws = 32 || ws = 64 then
            ws
        else
            failwith <| "invalid word size " + string ws + ". Allowed values are 8, 16, 32, 64."
       

    let parser = 
        ArgumentParser.Create<BlechCArg>(programName = "blechc")
    
    type CommandLineHelp = string

    let collectOptions (argv : string[]) : Result<BlechCOptions, CommandLineHelp> =
        try
            let config = parser.ParseCommandLine(inputs = argv, raiseOnUsage = true)
    
            if config.Contains <@ Word_Size @> then 
                ignore <| config.PostProcessResult(<@ Word_Size @>, parseWordSize)
    
            let opts =
                config.GetAllResults()
                |> List.fold changeOptionFromArg BlechCOptions.Default
            
            Ok opts 
        with e ->
            Error e.Message