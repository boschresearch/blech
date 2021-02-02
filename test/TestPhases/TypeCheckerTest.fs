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

let runTypeChecker implOrIface moduleName filePath =
    let cliContext = Arguments.BlechCOptions.Default
    let logger = Diagnostics.Logger.create ()
    let options = 
        let projectDir = System.IO.Path.Combine(__SOURCE_DIRECTORY__, TestFiles.Typechecker.Directory)
        { Blech.Common.Arguments.BlechCOptions.Default with inputFile = filePath
                                                            sourcePath = projectDir 
                                                            projectDir = projectDir }

    let pkgCtx = CompilationUnit.Context.Make options (Blech.Compiler.Main.loader options)

    printfn "Source Directory: %s" __SOURCE_DIRECTORY__

    let ast = Blech.Frontend.ParsePkg.parseModuleFromFile logger implOrIface moduleName filePath
    Assert.True (Result.isOk ast)
    
    let importsRes =
        ast
        |> Result.bind (Blech.Compiler.Main.runImportCompilation pkgCtx logger CompilationUnit.ImportChain.Empty moduleName filePath)
                    
    match ast, importsRes with
    | Ok ast, Ok imports -> 
        
        let symTableRes =
            let lookupTables = imports.GetLookupTables
            let exportScopes = imports.GetExportScopes
            Blech.Compiler.Main.runNameResolution logger moduleName filePath lookupTables exportScopes ast
        Assert.True (Result.isOk symTableRes)
        
        let ncEnv = Result.getOk symTableRes
        let lut = TypeCheckContext.Init cliContext ncEnv
        imports.GetTypeCheckContexts
        |> List.iter (fun otherLut ->
            for pair in otherLut.nameToDecl do Blech.Frontend.TypeCheckContext.addDeclToLut lut pair.Key pair.Value
            for pair in otherLut.userTypes do Blech.Frontend.TypeCheckContext.addTypeToLut lut pair.Key (fst pair.Value) (snd pair.Value)
            for pragma in otherLut.memberPragmas do Blech.Frontend.TypeCheckContext.addPragmaToLut lut pragma
            )

        Blech.Frontend.TypeChecking.fPackage lut ast
    | _, Error errs
    | Error errs, _ ->
        printfn "Did not expect to find errors in imported files!\n" 
        Diagnostics.Emitter.printDiagnostics errs
        Error []

[<TestFixture>]
type Test() =

    /// load test cases for typeCheckValidFiles test
    static member validFiles =
        TestFiles.validFiles TestFiles.Typechecker
        
    /// run typeCheckValidFiles
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member x.TypeCheckValidFiles (implOrIface, moduleName, filePath) =
        match runTypeChecker implOrIface moduleName filePath with
        | Ok _ ->
            Assert.True true
        | Error errs ->
            printfn "Did not expect to find errors!\n" 
            let logger = Diagnostics.Logger.create ()
            Diagnostics.printErrors logger Diagnostics.Phase.Typing errs
            Assert.Fail()
        
    /// load test cases for typeCheckInvalidInputs test
    static member invalidFiles =
        TestFiles.invalidFiles TestFiles.Typechecker
        
    /// run typeCheckInvalidInputs
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "invalidFiles")>]
    member x.TypeCheckInvalidInputs (implOrIface, moduleName, filePath) =
        match runTypeChecker implOrIface moduleName filePath with
        | Ok _ ->
            Assert.True false
        | Error errs ->
            let logger = Diagnostics.Logger.create ()
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
                Assert.Pass()
            