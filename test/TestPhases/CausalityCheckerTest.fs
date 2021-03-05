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

module CausalityCheckerTest

open NUnit.Framework

open System.IO
open Blech.Common
open Blech.Compiler

let parseHandleImportsNameCheckAndTypeCheck logger cliContext pkgCtx implOrIface moduleName fileName = 
    let importChain = CompilationUnit.ImportChain.Empty
    let fileContents = File.ReadAllText <| Path.GetFullPath fileName

    let resultWorkflow = ResultBuilder()
    resultWorkflow {
        let! ast =
            Main.runParser 
                logger 
                implOrIface
                moduleName 
                fileContents 
                fileName

        let! imports =
            Main.runImportCompilation 
                pkgCtx 
                logger 
                importChain
                moduleName 
                fileName
                ast

        let! symTable =
            Main.runNameResolution 
                logger 
                moduleName 
                fileName 
                imports.GetLookupTables
                imports.GetExportScopes
                ast

        let! singletons, abstractTypes = 
            Main.runOpaqueInference 
                logger 
                fileName 
                imports.GetSingletons 
                imports.GetAbstractTypes
                ast
                symTable
        // no export inference needed

        let! lut, blechModule = 
            Main.runTypeChecking 
                cliContext
                logger
                fileName
                imports.GetTypeCheckContexts
                ast
                symTable
                singletons

        return lut, blechModule
    }


let runCausalityAnalysis implOrIface moduleName fileName =
    let logger = Diagnostics.Logger.create ()
    let cliContext = 
        { 
            TestFiles.makeCliContext TestFiles.Causality.Directory fileName with 
                isDryRun = true // no code generation necessary        
        }
    let pkgCtx = CompilationUnit.Context.Make cliContext <| Main.loader cliContext
    
    match parseHandleImportsNameCheckAndTypeCheck logger cliContext pkgCtx implOrIface moduleName fileName with
    | Ok (lut, blechModule) ->
        Main.runCausalityCheck logger fileName lut blechModule
    | Error logger ->
        printfn "Did not expect to find errors during parsing, name checking, typeChecking or in imported files!\n" 
        do Diagnostics.Emitter.printDiagnostics logger
        do List.iter TestFiles.printImportDiagnostics pkgCtx.GetErrorImports
        
        Assert.False true
        Error logger


[<TestFixture>]
type Test() =

    /// load test cases for causalityCheckValidFiles test
    static member validFiles = 
        TestFiles.validFiles TestFiles.Causality

    /// run causality analysis on valid files
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member __.CausalityCheckValidFiles (implOrIface, moduleName, filePath) =
        match runCausalityAnalysis implOrIface moduleName filePath with
        | Ok pgs ->
            pgs.Values
            |> Seq.map Blech.Intermediate.BlockGraph.buildFromPG
            |> Seq.iter (fun ctx -> printf "%s\n" (ctx.blockGraph.ToString()))
            Assert.True true
        | Error logger ->
            printfn "Did not expect to find errors!\n" 

            Diagnostics.Emitter.printDiagnostics logger
            Assert.True false

    /// load test cases for causalityCheckInvalidInputs test
    static member invalidFiles = 
        TestFiles.invalidFiles TestFiles.Causality

    /// run causality analysis on invalid files
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "invalidFiles")>]
    member __.CausalityCheckInvalidFiles (implOrIface, moduleName, filePath) =
        match runCausalityAnalysis implOrIface moduleName filePath with
        | Ok pgs ->
            pgs.Values |> Seq.iter (fun pg -> printf "%s\n" (pg.ToString()))
            Assert.True false
        | Error logger ->
            printfn "Discovered Errors:\n" 
            Diagnostics.Emitter.printDiagnostics logger
            Assert.True true