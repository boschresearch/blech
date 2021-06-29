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

open System.IO
open Blech.Common
open Blech.Compiler
open Blech.Frontend

let parseHandleImportsAndNameCheck pkgCtx logger implOrIface moduleName fileName = 
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
    
        return ast, imports, symTable, singletons
    }


let runTypeChecker logger implOrIface moduleName fileName =
    let cliContext = 
        {
            TestFiles.makeCliContext TestFiles.Typechecker.Directory fileName with
                isDryRun = true // no code generation necessary
        }
    let pkgCtx = CompilationUnit.Context.Make cliContext <| Main.loader cliContext
    
    match parseHandleImportsAndNameCheck pkgCtx logger implOrIface moduleName fileName with
    | Ok (ast, imports, symTable, singletons) -> 
        TypeChecking.typeCheckUnLogged
            cliContext
            imports.GetTypeCheckContexts 
            ast 
            symTable
            singletons

    | Error logger ->
        printfn "Did not expect to find errors during parsing, name checking, or in imported files!\n" 
        do Diagnostics.Emitter.printDiagnostics logger
        do List.iter TestFiles.printImportDiagnostics pkgCtx.GetErrorImports
        Assert.False true
        Error []


[<TestFixture>]
type Test() =

    /// load test cases for typeCheckValidFiles test
    static member validFiles =
        TestFiles.validFiles TestFiles.Typechecker
        
    /// run typeCheck on valid files
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member __.TypeCheckValidFiles (implOrIface, moduleName, filePath) =
        let logger = Diagnostics.Logger.create ()
        match runTypeChecker logger implOrIface moduleName filePath with
        | Ok _ ->
            Assert.True true
        | Error errs ->
            printfn "Did not expect to find errors!\n" 
            Diagnostics.printErrors logger Diagnostics.Phase.Typing errs
            Assert.Fail()
        
    /// load test cases for typeCheckInvalidInputs test
    static member invalidFiles =
        TestFiles.invalidFiles TestFiles.Typechecker
        
    /// run typeCheck on invalid files
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "invalidFiles")>]
    member __.TypeCheckInvalidFiles (implOrIface, moduleName, filePath) =
        let logger = Diagnostics.Logger.create ()
        match runTypeChecker logger implOrIface moduleName filePath with
        | Ok _ ->
            Assert.True false
        | Error errs ->
            let isUndesiredError e =
                match e with
                | ImpossibleCase _ 
                | UnsupportedFeature _ 
                | UnsupportedTuple _
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
            