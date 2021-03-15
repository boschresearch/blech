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

module ImportCheckTest

open NUnit.Framework

open System.IO
open Blech.Compiler
open Blech.Common
           
let private parseFile logger implOrIface moduleName fileName = 
    let fileContents = File.ReadAllText <| Path.GetFullPath fileName
    
    let resultWorkflow = ResultBuilder()
    resultWorkflow { // a one-step workflow, just for consistency with other tests
        let! ast =
            Main.runParser 
                logger 
                implOrIface
                moduleName 
                fileContents 
                fileName

        return ast
    }
    
let private runImportChecking pkgCtx implOrIface moduleName fileName = 
    let logger = Diagnostics.Logger.create ()
    let importChain = CompilationUnit.ImportChain.Empty
    
    match parseFile logger implOrIface moduleName fileName with
    | Ok ast -> 
        Main.runImportCompilation pkgCtx logger importChain moduleName fileName ast 
    | Error logger ->
        printfn "Did not expect to find errors during parsing\n" 
        do Diagnostics.Emitter.printDiagnostics logger
        
        Assert.False true
        Error logger
      
    
[<TestFixture>]
type Test() =

    /// load test cases for nameCheckValidFiles test
    static member validFiles =
        TestFiles.validFiles TestFiles.ImportChecker
    
    
    /// run nameCheckValidFiles
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member __.ImportCheckerValidFiles (implOrIface, moduleName, filePath) =
        let cliContext = 
            { 
                TestFiles.makeCliContext TestFiles.ImportChecker.Directory filePath with
                    isFrontendTest = true // no need for type checking and following phases
            }
                            
        let pkgCtx = CompilationUnit.Context.Make cliContext <| Main.loader cliContext
    
        match runImportChecking pkgCtx implOrIface moduleName filePath with
        | Error logger ->
            Diagnostics.Emitter.printDiagnostics logger
            do List.iter TestFiles.printImportDiagnostics pkgCtx.GetErrorImports
            
            Assert.False true
        | Ok imports ->
            Assert.True true
            
    /// load test cases for nameCheckInvalidInputs test
    static member invalidFiles = 
        TestFiles.invalidFiles TestFiles.ImportChecker
        
    /// run nameCheckInvalidInputs
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "invalidFiles")>]
    member __.ImportCheckerInvalidInputs (implOrIface, moduleName, filePath) =
        let cliContext = 
            { 
                TestFiles.makeCliContext TestFiles.ImportChecker.Directory filePath with
                    isFrontendTest = true // no need for type checking and following phases
            }
                            
        let pkgCtx = CompilationUnit.Context.Make cliContext <| Main.loader cliContext
    
        match runImportChecking pkgCtx implOrIface moduleName filePath with
        | Error logger ->
            Diagnostics.Emitter.printDiagnostics logger
            do List.iter TestFiles.printImportDiagnostics pkgCtx.GetErrorImports
            
            Assert.True true
        | Ok imports ->
            Assert.False true



