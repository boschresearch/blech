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

module NameCheckerTest

open NUnit.Framework

open Blech.Common
open Blech.Frontend

[<TestFixture>]
type Test() =

    /// load test cases for typeCheckValidFiles test
    static member validFiles =
        TestFiles.validFiles TestFiles.Namecheck
        
    /// run typeCheckValidFiles
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member x.typeCheckValidFiles (loadWhat, moduleName, filePath) =
        let logger = Diagnostics.Logger.create ()
        
        let ast = Blech.Frontend.ParsePkg.parseModule logger loadWhat moduleName filePath
        Assert.True (Result.isOk ast)
        
        let astAndEnv = 
            let ctx = Blech.Frontend.NameChecking.initialise logger moduleName
            Result.bind (Blech.Frontend.NameChecking.checkSingleFileDeclaredness ctx) ast
        match astAndEnv with
        | Error logger ->
            Diagnostics.Emitter.printDiagnostics logger
            Assert.False true
        | Ok (ast, env) ->
            printfn "%s" env.Show
            Assert.True true
            
    /// load test cases for typeCheckInvalidInputs test
    static member invalidFiles = 
        TestFiles.invalidFiles TestFiles.Namecheck
        
    /// run typeCheckInvalidInputs
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "invalidFiles")>]
    member x.typeCheckInvalidInputs (loadWhat, moduleName, filePath) =
        let logger = Diagnostics.Logger.create ()
        
        let ast = Blech.Frontend.ParsePkg.parseModule logger loadWhat moduleName filePath
        Assert.True (Result.isOk ast)

        let astAndEnv = 
            let ctx = Blech.Frontend.NameChecking.initialise logger moduleName
            Result.bind (Blech.Frontend.NameChecking.checkSingleFileDeclaredness ctx) ast
        match astAndEnv with
        | Error logger ->
            Diagnostics.Emitter.printDiagnostics logger
            Assert.True true
        | Ok (ast, env) ->
            printfn "%s" env.Show
            Assert.False true

        
    