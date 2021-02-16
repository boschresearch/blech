// Copyright (c) 2020 - for information on the respective copyright owner
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

let BLECH_SUFFIX = ".blc"
let C_SUFFIX = ".c"
let OBJ_SUFFIX = ".obj"
let EXE_SUFFIX = ".exe"
let EXT_SUFFIX = ".ext"
let IMP_SUFFIX = "_imp"
let EXT_C = EXT_SUFFIX + ".c"
let EXT_H = EXT_SUFFIX + ".h"
let IMP_C = IMP_SUFFIX + ".c"
let APP_NAME = "App"
let SPEC_SUFFIX = ".spec.json"
let TEST_SUFFIX = ".test.json"
let CUR_DIR = "" //default setting for ProcessStartInfo.WorkingDirectory

module DiffJSON =

    open FSharp.Data

    type TraceFormat = JsonProvider<"trace.json">

    type NameOrIndex =
        | Name of string
        | Index of int

    type ErrorType = 
        | NameMismatch
        | ValueMismatch
        | TypeMismatch
        | CardinalityMismatch

    type Error = NameOrIndex list * NameOrIndex list * ErrorType

    let rec private getNameFor path =
        let nOrX2str x =
            match x with
            | Name n -> n
            | Index i -> "[" + string i + "]"
        List.map nOrX2str path
        |> String.concat "."

    let rec private getVariableName path =
        match path with
        | [] -> failwith "Empty path"
        | [n] ->
            match n with
            | Name name -> name
            | Index _ -> failwith "Expected name, got index!"
        | _ :: xs -> getVariableName xs

    let rec private getValueFor (j: JsonValue) path =
        match path with
        | [] -> j.ToString()
        | Name n :: rest -> j.GetProperty n |> getValueFor <| rest
        | Index i :: rest -> j.AsArray() |> Array.get <| i |> getValueFor <| rest

    let private getTickNumber (j1: JsonValue) (path: NameOrIndex list) =
        let index = 
            match path.[1] with
            | Index i -> i
            | _ -> failwith "Expected index, got name!"
        j1.GetProperty("trace")
        |> (fun x -> x.AsArray())
        |> Array.get <| index
        |> (fun x -> x.GetProperty "tick")
        |> string

    let private printError err j1 j2 =
        let path1, path2, typ = err
        let name1 = getNameFor path1
        let name2 = getNameFor path2
        match typ with
        | NameMismatch ->
            printfn "Original trace has a name %s which the new trace cannot match - closest is %s." name1 name2
        | ValueMismatch ->
            let val1 = getValueFor j1 path1
            let val2 = getValueFor j2 path2
            let varName = getVariableName path1
            let tick = getTickNumber j1 path1
            printfn "Value mismatch in tick %s, variable %s, spec %s, test %s." tick varName val1 val2
        | TypeMismatch ->
            printfn "Original %s has a different type than %s." name1 name2
        | CardinalityMismatch ->
            printfn "Original %s has a different number of subelements than %s." name1 name2

    let private report path1 path2 errtyp : Error =
        //sprintf "(%s = %s, %s = %s)" n1 (j1.ToString()) n2 (j2.ToString())
        List.rev path1, List.rev path2, errtyp
    let rec private areJsonValuesEqual n1 n2 (j1: JsonValue) (j2: JsonValue) =
        match j1 with
        | JsonValue.String s1 ->
            match j2 with
            | JsonValue.String s2 -> if s1 = s2 then [] else [report n1 n2 ValueMismatch]
            | _ -> [report n1 n2 TypeMismatch]
        | JsonValue.Number x1 ->
            match j2 with
            | JsonValue.Number x2 -> if x1 = x2 then [] else [report n1 n2 ValueMismatch]
            | _ -> [report n1 n2 TypeMismatch]
        | JsonValue.Float f1 ->
            match j2 with
            | JsonValue.Float f2 -> if f1 = f2 then [] else [report n1 n2 ValueMismatch]
            | _ -> [report n1 n2 TypeMismatch]
        | JsonValue.Record prop1 ->
            match j2 with
            | JsonValue.Record prop2 -> 
                if prop1.Length = prop2.Length then
                    let sorted1 = Array.sortBy (fun (key, _) -> key) prop1
                    let sorted2 = Array.sortBy (fun (key, _) -> key) prop2
                    Array.map2 (
                        fun (k1, v1) (k2, v2) ->
                            if k1 = k2 then
                                areJsonValuesEqual (Name k1 :: n1) (Name k2 :: n2) v1 v2
                            else
                                [report (Name k1 :: n1) (Name k2 :: n2) NameMismatch]
                        ) sorted1 sorted2
                    |> Array.fold (fun state res -> match res with [] -> state | x -> x @ state) []
                else
                   [report n1 n2 CardinalityMismatch] 
            | _ -> [report n1 n2 TypeMismatch]
        | JsonValue.Array a1 ->
            match j2 with
            | JsonValue.Array a2 ->
                if a1.Length = a2.Length then
                    Array.mapi2 (fun idx v1 v2 -> areJsonValuesEqual (Index idx :: n1) (Index idx :: n2) v1 v2) a1 a2
                    |> Array.fold (fun state res -> match res with [] -> state | x -> x @ state) []
                else
                    [report n1 n2 CardinalityMismatch] 
            | _ -> [report n1 n2 TypeMismatch]
        | JsonValue.Boolean b1 ->
            match j2 with
            | JsonValue.Boolean b2 -> if b1 = b2 then [] else [report n1 n2 ValueMismatch]
            | _ -> [report n1 n2 TypeMismatch]
        | JsonValue.Null ->
            match j2 with
            | JsonValue.Null -> []
            | _ -> [report n1 n2 TypeMismatch]

    let getTrace fileName =
        try
            fileName
            |> System.IO.File.ReadAllText
            |> TraceFormat.Parse
        with
        | _ -> 
            printfn "Error reading file %s" fileName
            exit 0

    let private filterDifference (specification: TraceFormat.Root) (testResult: TraceFormat.Root) diffRes =
        let filterError err =
            printError err specification.JsonValue testResult.JsonValue
            let path1,_,typ = err
            if typ = ValueMismatch then
                Some path1
            else
                None
        match diffRes with
        | [] -> []
        | ds -> 
            ds
            |> List.map (filterError)
            |> List.choose id

    /// <summary>Compares the two given traces and returns a list of variables for which there is a value mismatch in some tick(s).</summary>
    /// <param name="specification">The trace from the specification.</param>
    /// <param name="testResult">The trace from the execution of the test.</param>
    /// <returns>Variable names.</returns>
    let diff (specification: TraceFormat.Root) (testResult: TraceFormat.Root) =
        let rootPath = [Name "trace"]
        (specification.Trace, testResult.Trace)
        ||> Array.mapi2 (
            fun i elemOrig elemTest -> 
                let path = [Name "vars"; Index i] @ rootPath
                areJsonValuesEqual path path elemOrig.Vars.JsonValue elemTest.Vars.JsonValue
                |> filterDifference specification testResult
            )
        |> Array.filter (fun x -> x <> [])
        |> Seq.concat
        |> Seq.toList
        |> List.map (getVariableName)
        |> List.distinct

module CompilationProcedures =
    open System
    open System.Diagnostics

    type ArgumentsStyle =
        | GCC
        | CL

    type Config =
        { blechc: string
          blcHeaders: string
          cc: string
          ccStyle: ArgumentsStyle
          extraCargs: string }
    
    /// Given a name for a command, its arguments and a working directory
    /// run this command and return a pair of stdout and stderr outputs
    let execInCLI filename args workDir = 
        
        let procStartInfo = 
            ProcessStartInfo(
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
                FileName = filename,
                WorkingDirectory = workDir,
                Arguments = args
            )
        
        let outputs = ResizeArray<string>()
        let errors = ResizeArray<string>()
        let handler f _ (args:DataReceivedEventArgs) = f args.Data
        
        use cliProcess = new Process(StartInfo = procStartInfo)
        cliProcess.OutputDataReceived.AddHandler(DataReceivedEventHandler (handler outputs.Add))
        cliProcess.ErrorDataReceived.AddHandler(DataReceivedEventHandler (handler errors.Add))
        
        let hasStarted = 
            try
                cliProcess.Start()
            with
                | _ -> reraise()
        if not hasStarted then
            failwithf "Failed to start process %s" filename

        cliProcess.BeginOutputReadLine()
        cliProcess.BeginErrorReadLine()
        cliProcess.WaitForExit()
        
        let removeEmpty (ra:ResizeArray<string>) = ra.RemoveAll(new Predicate<_>(String.IsNullOrEmpty)) |> ignore
        removeEmpty outputs
        removeEmpty errors
        outputs, errors
    
    let runBLCcompiler config (testcase: string) outDir =
        let inputFile = System.IO.Path.GetFileName(testcase)
        let inputModule = System.IO.Path.GetFileNameWithoutExtension(testcase)
        let sourcePath = System.IO.Path.GetDirectoryName(testcase)
        let appName = inputModule + APP_NAME
        
        // By convention, external C code, if any, is in files inputModule.ext.c, inputModule.ext.h
        // If that exists, copy it to the destination folder where the C sources are placed
        let cExtern = System.IO.Path.Combine(sourcePath, inputModule) + EXT_C
        if System.IO.File.Exists cExtern then
            let destCextern = System.IO.Path.Combine(outDir, inputModule) + EXT_C
            System.IO.File.Copy(cExtern, destCextern, true) // overwrite if already exists
        let hExtern = System.IO.Path.Combine(sourcePath, inputModule) + EXT_H
        if System.IO.File.Exists hExtern then
            let destHextern = System.IO.Path.Combine(outDir, inputModule) + EXT_H
            System.IO.File.Copy(hExtern, destHextern, true) // overwrite if already exists

        // first clean any previous compilation results
        let cCode = System.IO.Path.Combine(outDir, inputModule) + C_SUFFIX
        if System.IO.File.Exists cCode then
            System.IO.File.Delete cCode
        
        // now compile the test case
        let dotnet = "dotnet"
        let args =  config.blechc
                    // no need to set the source path as we run the CLI in the source path, see below
                    + " --out-dir " + outDir 
                    + " --app=" + appName
                    + " --trace"
                    + " " + inputFile
        let out, _ = execInCLI dotnet args sourcePath
        out |> String.concat "\n" |> printf "%s" 
        ()
        
    
    let runCcompiler config (testcase: string) outDir =
        let noPathtestcase = System.IO.Path.GetFileNameWithoutExtension(testcase)
        // first clean any previous compilation results
        let app = System.IO.Path.Combine(outDir, noPathtestcase + APP_NAME + EXE_SUFFIX)
        if System.IO.File.Exists app then
            System.IO.File.Delete app
        // now compile the test case
        let moduleName = System.IO.Path.Combine(outDir, noPathtestcase)
        let cExtern = moduleName + EXT_C
        let maybeExtern =
            if System.IO.File.Exists cExtern then cExtern
            else ""
        let cImported = moduleName + IMP_C
        let maybeImported =
            if System.IO.File.Exists cImported then cImported
            else ""
        let cApp = moduleName + APP_NAME + C_SUFFIX
        
        if System.IO.File.Exists cApp then
            let incDir = config.blcHeaders
            let args = 
                match config.ccStyle with
                | CL ->
                    config.extraCargs
                    + " /I " + incDir 
                    + " /I " + outDir
                    + " /Fo" + outDir + @"\" 
                    + " /Fe" + outDir + @"\" 
                    + " " + cApp
                    + " " + maybeExtern
                    + " " + maybeImported
                | GCC ->
                    config.extraCargs
                    + " -I " + incDir 
                    + " -I " + outDir
                    + " -o" + app
                    + " " + cApp
                    + " " + maybeExtern
                    + " " + maybeImported
            let outputMsgs, errorMsgs = execInCLI config.cc args CUR_DIR
            // glue messages together, if they contain at least one line saying "error" or "warning", print them
            let allMsgs = Seq.concat [outputMsgs; errorMsgs]
            if allMsgs |> Seq.exists (fun msg -> msg.ToLowerInvariant().Contains "error" || msg.ToLowerInvariant().Contains "warning") then
                allMsgs |> Seq.iter(fun msg -> printfn "%s\n" msg)
            ()
        else
            printfn "The test case %s does not exist." cApp
            exit 0
        // clean obj files
        let objFile = moduleName + OBJ_SUFFIX
        let objImport = moduleName + IMP_SUFFIX + OBJ_SUFFIX
        let objAppFile = moduleName + APP_NAME + OBJ_SUFFIX
        if System.IO.File.Exists objFile then
            System.IO.File.Delete objFile
        if System.IO.File.Exists objImport then
            System.IO.File.Delete objImport
        if System.IO.File.Exists objAppFile then
            System.IO.File.Delete objAppFile
    
    
    let runTestcase (testcase: string) outDir =
        let noPathtestcase = System.IO.Path.GetFileNameWithoutExtension(testcase)
        let app = System.IO.Path.Combine(outDir, noPathtestcase + APP_NAME + EXE_SUFFIX)
        if System.IO.File.Exists app then
            let workingDir = outDir
            let lines, _ = execInCLI app "" workingDir
            let output = String.concat "\n" lines
            let testjson = System.IO.Path.Combine(outDir, noPathtestcase + TEST_SUFFIX)
            System.IO.File.WriteAllText (testjson, output)
            ()
        else
            printfn "The compilation of %s has failed." app
            exit 0

module RunTests =
    
    open CompilationProcedures
    open DiffJSON
    
    let processFile config outputDir (file: string) =
        let noPathFile = System.IO.Path.GetFileName file
        let noPathNoExtensionFile = System.IO.Path.GetFileNameWithoutExtension file
        printfn "Processing %s." noPathFile
        // check that a spec trace exists
        let extensionLength = BLECH_SUFFIX.Length
        let noExtensionFile = file.Remove(file.Length - extensionLength, extensionLength)
        let specjson = noExtensionFile + SPEC_SUFFIX
        let testjson = System.IO.Path.Combine(outputDir, noPathNoExtensionFile + TEST_SUFFIX)
        if System.IO.File.Exists (specjson) then
            // compile and generate trace, compare with spec trace
            runBLCcompiler config file outputDir
            runCcompiler config file outputDir
            runTestcase file outputDir
            if System.IO.File.Exists (testjson) then
                let specification = getTrace (specjson)
                let testResult = getTrace (testjson)
                ignore <| diff specification testResult
                // no charting done to make this script portable
            else
                printfn "Compiled %s but no trace has been generated." file
        else
            printfn "Skipping %s because the specified trace to test against was not found." file
    // if difference found, report and plot

    let processFiles c fs d = 
        let mutable errors = 0
        fs 
        |> Array.iter(fun f -> 
            try
                processFile c d f
            with
            | e -> 
                eprintfn "%s" (e.ToString())
                errors <- errors + 1
        )
        errors

open CompilationProcedures

let createConfig() =
    let rec readCC() =
        System.Console.WriteLine "Please enter the command that invokes the C compiler on your machine (e.g. gcc or cl.exe)."
        System.Console.WriteLine "Note that on Windows you need to run this program inside the Developer Command Prompt if the C compiler is available only there."
        let cc = System.Console.ReadLine()
        try
            let _ = execInCLI cc "" CUR_DIR
            cc
        with
            | _ -> 
                System.Console.WriteLine ("ERROR: failed to invoke " + cc)
                readCC() // try again

    let rec readStyle() =
        System.Console.WriteLine "Does your compiler use gcc style arguments (-I, -o) or Windows cl like arguments (/I /Fe /Fo)?"
        System.Console.WriteLine "Enter option [gcc / cl]"
        let input = System.Console.ReadLine()
        let normalisedInput = input.Trim().ToLowerInvariant()
        if normalisedInput.Contains("gcc") then
            System.Console.WriteLine("Assuming gcc style.")
            GCC
        elif normalisedInput.Contains("cl") then
            System.Console.WriteLine("Assuming cl style.")
            CL
        else
            System.Console.WriteLine("ERROR: Choice unclear. Enter either \"gcc\" or \"cl\".")
            readStyle()

    let readExtra() = 
        System.Console.WriteLine "You may define extra arguments to pass to the C compiler. Simply hit ENTER for none."
        System.Console.WriteLine "For example: -std=c89 -pedantic -Wall -Wno-long-long -Wno-unused-variable -Wno-unused-function -Wno-unused-value -Wno-format -Wno-format-extra-args -Wno-char-subscripts"
        System.Console.ReadLine()

    try
        let writer = System.IO.File.CreateText("config")
        writer.AutoFlush <- true
        let defaultBlechcLocation = 
            System.IO.Path.Combine [| "..";"..";"src";"blechc";"bin";"Debug";
                                      "netcoreapp3.1";"blechc.dll" |]
            |> System.IO.Path.GetFullPath
        let defaultIncludeLocation =
            System.IO.Path.Combine [| "..";"..";"src";"blechc";"include" |]
            |> System.IO.Path.GetFullPath
        System.Console.WriteLine ("Writing default location of blechc compiler to config: \n\t" + defaultBlechcLocation)
        writer.WriteLine defaultBlechcLocation
        System.Console.WriteLine ("Writing default include path of blech headers to config: \n\t" + defaultIncludeLocation)
        writer.WriteLine defaultIncludeLocation
        let cc = readCC()
        writer.WriteLine cc
        let style = readStyle()
        writer.WriteLine style
        let extra = readExtra()
        writer.WriteLine extra
        writer.Close()

    with
        | _ -> failwith "Cannot create config file."
    
let parseConfig() =
    let allLines = System.IO.File.ReadAllLines "config" // we assume this file exists since we have just created it
    if allLines.Length < 4 then
        failwith "Corrupted config file. Delete it and rerun this program."
    else
        let style = 
            if allLines.[3].Equals (GCC.ToString()) then GCC
            elif allLines.[3].Equals (CL.ToString()) then CL
            else failwith "Corrupted config file. Delete it and rerun this program."
        let extra =
            if allLines.Length >= 5 then allLines.[4]
            else ""
        { blechc = allLines.[0]
          blcHeaders = allLines.[1]
          cc = allLines.[2]
          ccStyle = style
          extraCargs = extra }

open RunTests

[<EntryPoint>]
let main argv =
    let programArgs = argv
    if programArgs.Length < 2 then
        printfn "Requires two parameters: dotnet run -- {input_folder | input_file} output_folder"
        exit 0

    // create or open config file that contains user-specific paths
    if not <| System.IO.File.Exists "config" then
        createConfig()
    let config = parseConfig()
    
    let path = programArgs.[0]
    let outputPath = 
        let givenOutPath = programArgs.[1]
        // Ensure the output directory exists
        if System.IO.Directory.Exists givenOutPath then
            // ok!
            givenOutPath
            |> System.IO.Path.GetFullPath
        else
            try
                System.IO.Directory.CreateDirectory givenOutPath 
                |> (fun info -> info.FullName)
            with
            | _ ->
                printfn "Cannot create output path %s." givenOutPath
                exit 0
    
    // determine whether we are in single file or whole folder mode
    if System.IO.Directory.Exists path then
        // directory mode
        // folder where all *.blc and *.spec.json files are
        let files =
            System.IO.Directory.GetFiles path
            |> Array.filter (fun s -> s.EndsWith BLECH_SUFFIX)
        if files.Length = 0 then
            printfn "No *%s files were found in directory %s." BLECH_SUFFIX path
        else
            let exceptions = processFiles config files outputPath
            if exceptions > 0 then
                printfn "%i exceptions occurred while processing %s." exceptions path
    elif System.IO.File.Exists path then
        // file mode
        if path.EndsWith BLECH_SUFFIX then
            let exceptions = processFiles config [|path|] outputPath
            if exceptions > 0 then
                printfn "%i exceptions occurred while processing %s." exceptions path
        else
            printfn "Given file %s is not a *%s file." path BLECH_SUFFIX
            
    else
        printfn "The given argument %s neither is a file nor a directory." path
        
    exit 0
