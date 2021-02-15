﻿// Copyright (c) 2019 - for information on the respective copyright owner
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

module SingletonInferenceTest

open NUnit.Framework

open System.IO
open Blech.Common
open Blech.Compiler
//open Blech.Frontend

let private parseNameCheckAndHandleImports logger implOrIface moduleName fileName =
    let cliContext = 
        { 
            TestFiles.makeCliContext TestFiles.SingletonInference.Directory fileName with 
                isFrontendTest = true // stop before typecheck for imports
        }
    let pkgCtx = CompilationUnit.Context.Make cliContext <| Main.loader cliContext
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
        return ast, imports, symTable
    }

let runSingletonInference implOrIface moduleName fileName =
    let logger = Diagnostics.Logger.create ()

    match parseNameCheckAndHandleImports logger implOrIface moduleName fileName with
    | Ok (ast, imports, symTable) -> 
        Main.runSingletonInference
            logger 
            fileName 
            imports.GetSingletons 
            ast
            symTable
    | Error logger ->
        printfn "Did not expect to find errors during parsing, name checking, or in imported files!\n" 
        Diagnostics.Emitter.printDiagnostics logger
        Assert.False true
        Error logger

    
[<TestFixture>]
type Test() =

    /// load test cases for nameCheckValidFiles test
    static member validFiles =
        TestFiles.validFiles TestFiles.SingletonInference
        
    /// run nameCheckValidFiles
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member __.SingletonInferenceValidFiles (implOrIface, moduleName, filePath) =
        match runSingletonInference implOrIface moduleName filePath with
        | Error logger ->
            printfn "Did not expect to find errors!\n" 
            Diagnostics.Emitter.printDiagnostics logger
            Assert.True false
        | Ok _ ->
            Assert.True true
            
    /// load test cases for nameCheckInvalidInputs test
    static member invalidFiles = 
        TestFiles.invalidFiles TestFiles.SingletonInference
        
    /// run nameCheckInvalidInputs
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "invalidFiles")>]
    member __.SingletonInferencencInvalidFiles (implOrIface, moduleName, filePath) =
        match runSingletonInference implOrIface moduleName filePath with
        | Error logger ->
            printfn "Discovered Errors:\n" 
            Diagnostics.Emitter.printDiagnostics logger
            Assert.True true
        | Ok _ ->
            Assert.True false
            