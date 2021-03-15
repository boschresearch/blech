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

open System.IO
open Blech.Common
open Blech.Compiler


let private parseHandleImportsNameCheckAndInferSingletons pkgCtx logger implOrIface moduleName fileName =
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
        
        return ast, imports, symTable, singletons, abstractTypes
    }


let inferExports implOrIface moduleName fileName =
    let logger = Diagnostics.Logger.create ()
    let cliContext = 
        { 
            TestFiles.makeCliContext TestFiles.ExportInference.Directory fileName with 
                isFrontendTest = true // stop before typecheck for imports
        }
    let pkgCtx = CompilationUnit.Context.Make cliContext <| Main.loader cliContext

    match parseHandleImportsNameCheckAndInferSingletons pkgCtx logger implOrIface moduleName fileName with
    | Ok (ast, imports, symTable, singletons, abstractTypes) -> 
        Main.runExportInference 
            logger 
            symTable 
            fileName 
            singletons // subsumes imported singletons
            abstractTypes
            imports.GetImportedInternalModules
            ast
    
    | Error logger ->
        printfn "Did not expect to find errors during parsing, name checking, singleton inference or in imported files!\n" 
        do Diagnostics.Emitter.printDiagnostics logger
        do List.iter TestFiles.printImportDiagnostics pkgCtx.GetErrorImports
        
        Assert.False true
        Error logger


[<TestFixture>]
type Test() =

    /// load test cases for nameCheckValidFiles test
    static member validFiles =
        TestFiles.validFiles TestFiles.ExportInference
        
    /// run nameCheckValidFiles
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member __.ExportInferencValidFiles (implOrIface, moduleName, filePath) =
        match inferExports implOrIface moduleName filePath with
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
    member __.ExportInferenceInvalidFiles (implOrIface, moduleName, filePath) =
        match inferExports implOrIface moduleName filePath with
        | Error logger ->
            printfn "Discovered Errors:\n" 
            Diagnostics.Emitter.printDiagnostics logger
            Assert.True true
        | Ok _ ->
            Assert.True false
            