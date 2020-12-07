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

open Blech.Common

[<TestFixture>]
type Test() =

    /// load test cases for causalityCheckValidFiles test
    static member validFiles = 
        TestFiles.validFiles TestFiles.Causality

        
    /// run causalityCheckValidFiles
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member x.causalityCheckValidFiles (implOrIface, moduleName, filePath) =
        let cliContext = Arguments.BlechCOptions.Default

        let logger = Diagnostics.Logger.create ()
        
        let ast = Blech.Frontend.ParsePkg.parseModuleFromFile logger implOrIface moduleName filePath
        Assert.True (Result.isOk ast)

        let astAndEnv = 
            let ctx = Blech.Frontend.NameChecking.initialise logger moduleName Map.empty Map.empty
            // Result.bind (Blech.Frontend.NameChecking.checkSingleFileDeclaredness ctx) ast
            Result.bind (Blech.Frontend.NameChecking.checkDeclaredness ctx) ast
        Assert.True (Result.isOk astAndEnv)
        
        let lutAndTyPkg = 
            Result.bind (Blech.Frontend.TypeChecking.typeCheck cliContext logger []) astAndEnv 
        Assert.True (Result.isOk lutAndTyPkg)
        
        let progGraphs = 
            Result.bind 
            <| Blech.Intermediate.Causality.checkPackCausality logger
            <| lutAndTyPkg
        
        //let causalityContext = Blech.Intermediate.ProgramGraph.createPGofPackage lut blechPack
        //match Blech.Intermediate.Causality.checkPackCausality causalityContext with
        match progGraphs with
        | Ok pgs ->
            pgs.Values
            |> Seq.map Blech.Intermediate.BlockGraph.buildFromPG
            |> Seq.iter (fun ctx -> printf "%s\n" (ctx.blockGraph.ToString()))
            Assert.True true
        | Error logger ->
            Diagnostics.Emitter.printDiagnostics logger
            Assert.True false


    /// load test cases for causalityCheckInvalidInputs test
    static member invalidFiles = 
        TestFiles.invalidFiles TestFiles.Causality

        
    /// run causalityCheckInvalidInputs
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "invalidFiles")>]
    member x.causalityCheckInvalidInputs (implOrIface, moduleName, filePath) =
        let cliContext = Arguments.BlechCOptions.Default
        
        let logger = Diagnostics.Logger.create ()
        let ast = Blech.Frontend.ParsePkg.parseModuleFromFile logger implOrIface moduleName filePath
        Assert.True (Result.isOk ast)
        
        let astAndEnv = 
            let ctx = Blech.Frontend.NameChecking.initialise logger moduleName Map.empty Map.empty
            //Result.bind (Blech.Frontend.NameChecking.checkSingleFileDeclaredness ctx) ast
            Result.bind (Blech.Frontend.NameChecking.checkDeclaredness ctx) ast
        Assert.True (Result.isOk astAndEnv)
        
        let lutAndTyPkg = 
            Result.bind (Blech.Frontend.TypeChecking.typeCheck cliContext logger []) astAndEnv 
        Assert.True (Result.isOk lutAndTyPkg)
        
        let progGraphs = 
            Result.bind 
            <| Blech.Intermediate.Causality.checkPackCausality logger
            <| lutAndTyPkg
        
        match progGraphs with
        | Ok pgs ->
            pgs.Values |> Seq.iter (fun pg -> printf "%s\n" (pg.ToString()))
            Assert.True false
        | Error logger ->
            Diagnostics.Emitter.printDiagnostics logger
            Assert.True true
        
        

    

