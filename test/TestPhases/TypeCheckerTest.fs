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

module TypeCheckerTest

open NUnit.Framework

open Blech.Common
open Blech.Frontend

[<TestFixture>]
type Test() =

    /// load test cases for typeCheckValidFiles test
    static member validFiles =
        TestFiles.validFiles TestFiles.Typechecker
        
    /// run typeCheckValidFiles
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member x.typeCheckValidFiles (implOrIface, moduleName, filePath) =
        let cliContext = Arguments.BlechCOptions.Default

        let logger = Diagnostics.Logger.create ()
        
        let ast = Blech.Frontend.ParsePkg.parseModuleFromFile logger implOrIface moduleName filePath
        Assert.True (Result.isOk ast)
        
        let astAndEnv = 
            let ctx = Blech.Frontend.NameChecking.initialise logger moduleName Map.empty
            // Result.bind (Blech.Frontend.NameChecking.checkSingleFileDeclaredness ctx) ast
            Result.bind (Blech.Frontend.NameChecking.checkDeclaredness ctx) ast
        Assert.True (Result.isOk astAndEnv)
        
        let lutAndTyPkg = 
            Result.bind (Blech.Frontend.TypeChecking.typeCheck cliContext logger []) astAndEnv
        
        match lutAndTyPkg with
        | Ok _ ->
            Assert.True true
        | Error errs ->
            printfn "Did not expect to find errors!\n" 
            Diagnostics.Emitter.printDiagnostics errs
            Assert.True false
        
    /// load test cases for typeCheckInvalidInputs test
    static member invalidFiles =
        TestFiles.invalidFiles TestFiles.Typechecker
        
    /// run typeCheckInvalidInputs
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "invalidFiles")>]
    member x.typeCheckInvalidInputs (implOrIface, moduleName, filePath) =
        let blechcOptions = Arguments.BlechCOptions.Default
        
        let logger = Diagnostics.Logger.create ()
        
        let ast = Blech.Frontend.ParsePkg.parseModuleFromFile logger implOrIface moduleName filePath
        Assert.True (Result.isOk ast)
        
        let astAndEnv = 
            let ctx = Blech.Frontend.NameChecking.initialise logger moduleName Map.empty
            // Result.bind (Blech.Frontend.NameChecking.checkSingleFileDeclaredness ctx) ast
            Result.bind (Blech.Frontend.NameChecking.checkDeclaredness ctx) ast
        Assert.True (Result.isOk astAndEnv)
        
        match astAndEnv with
        | Error _ ->
            Assert.True false 
        | Ok (ast, env) ->
            let lut = TypeCheckContext.Init blechcOptions env
            let typedResult = Blech.Frontend.TypeChecking.fPackage lut ast
            match typedResult with
            | Ok _ ->
                Assert.True false
            | Error errs ->
                let isUndesiredError e =
                    match e with
                    | ImpossibleCase _ 
                    | UnsupportedFeature _ 
                    | UnsupportedTuple _
                    | IllegalAccessOfTypeInfo _ 
                    | ExpectedSubProgDecl _ 
                    | AmendBroken _
                    //| MissingQName _
                    | NoDefaultValueForAny _ 
                    | IllegalVoid _ 
                    | ValueCannotBeVoid _ 
                    | EmptyGuardList -> true
                    | _ -> false
                if errs |> List.exists isUndesiredError then
                    printfn "Errors did occur in this invalid test case, BUT NOT THE ONES WE EXPECTED!"
                    Diagnostics.printErrors logger Diagnostics.Phase.Typing errs
                    Assert.Fail()
                else
                    printfn "Discovered Errors:\n" 
                    Diagnostics.printErrors logger Diagnostics.Phase.Typing errs
                    Assert.True true
            