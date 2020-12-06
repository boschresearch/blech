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

module ExportInferenceTest

open NUnit.Framework

open Blech.Common
open Blech.Frontend

[<TestFixture>]
type Test() =

    /// load test cases for nameCheckValidFiles test
    static member validFiles =
        TestFiles.validFiles TestFiles.ExportInference
        
    /// run nameCheckValidFiles
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member x.nameCheckValidFiles (implOrIface, moduleName, filePath) =
        let logger = Diagnostics.Logger.create ()
        
        let ast = Blech.Frontend.ParsePkg.parseModuleFromFile logger implOrIface moduleName filePath
        Assert.True (Result.isOk ast)
        
        let astAndEnv = 
            let ctx = Blech.Frontend.NameChecking.initialise logger moduleName Map.empty
            Result.bind (Blech.Frontend.NameChecking.checkDeclaredness ctx) ast
        Assert.True (Result.isOk astAndEnv)

        let inferredExportRes = 
            astAndEnv
            |> Result.bind (fun (ast, env) -> ExportInference.inferExports logger env ast)

        match inferredExportRes with
        | Error logger ->
            printfn "Did not expect to find errors!\n" 
            Diagnostics.Emitter.printDiagnostics logger
            Assert.True false
        | Ok _ ->
            Assert.True true
            
    /// load test cases for nameCheckInvalidInputs test
    static member invalidFiles = 
        TestFiles.invalidFiles TestFiles.ExportInference
        
    /// run nameCheckInvalidInputs
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "invalidFiles")>]
    member x.nameCheckInvalidInputs (implOrIface, moduleName, filePath) =
        let logger = Diagnostics.Logger.create ()
        
        let ast = Blech.Frontend.ParsePkg.parseModuleFromFile logger implOrIface moduleName filePath
        Assert.True (Result.isOk ast)

        let astAndEnv = 
            let ctx = Blech.Frontend.NameChecking.initialise logger moduleName Map.empty
            Result.bind (Blech.Frontend.NameChecking.checkDeclaredness ctx) ast
        // Assert.True (Result.isOk astAndEnv)  // TODO: currently no invalid export inference test, that go beyond name checking

        let inferredExportRes = 
            astAndEnv
            |> Result.bind (fun (ast, env) -> ExportInference.inferExports logger env ast)

        match inferredExportRes with
        | Error logger ->
            printfn "Discovered Errors:\n" 
            Diagnostics.Emitter.printDiagnostics logger
            Assert.True true
        | Ok _ ->
            Assert.True false
            