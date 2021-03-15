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

open System.IO
open Blech.Compiler
open Blech.Common


let private parseFileAndHandleImports logger pkgCtx implOrIface moduleName fileName =
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
        return ast, imports
    }
           

let private runNameChecking implOrIface moduleName fileName = 
    let logger = Diagnostics.Logger.create ()
    let cliContext = 
        { 
            TestFiles.makeCliContext TestFiles.Namecheck.Directory fileName with 
                isFrontendTest = true // stop before typecheck for imports
        }
    let pkgCtx = CompilationUnit.Context.Make cliContext <| Main.loader cliContext
    
    match parseFileAndHandleImports logger pkgCtx implOrIface moduleName fileName with
    | Ok (ast, imports) -> 
        Main.runNameResolution 
            logger 
            moduleName 
            fileName 
            imports.GetLookupTables 
            imports.GetExportScopes
            ast
    | Error logger ->
        printfn "Did not expect to find errors during parsing or in imported files!\n" 
        do Diagnostics.Emitter.printDiagnostics logger
        do List.iter TestFiles.printImportDiagnostics pkgCtx.GetErrorImports
        
        Assert.False true
        Error logger
      
    
[<TestFixture>]
type Test() =

    /// load test cases for nameCheckValidFiles test
    static member validFiles =
        TestFiles.validFiles TestFiles.Namecheck
        
    /// run nameCheckValidFiles
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member __.NameCheckValidFiles (implOrIface, moduleName, filePath) =
        match runNameChecking implOrIface moduleName filePath with
        | Error logger ->
            Diagnostics.Emitter.printDiagnostics logger
            Assert.False true
        | Ok env ->
            // printfn "%s" (SymbolTable.Environment.getLookupTable env).Show
            Assert.True true
            
    /// load test cases for nameCheckInvalidInputs test
    static member invalidFiles = 
        TestFiles.invalidFiles TestFiles.Namecheck
        
    /// run nameCheckInvalidInputs
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "invalidFiles")>]
    member __.NameCheckInvalidFiles (implOrIface, moduleName, filePath) =
        match runNameChecking implOrIface moduleName filePath with
        | Error logger ->
            Diagnostics.Emitter.printDiagnostics logger
            Assert.True true
        | Ok env ->
            // printfn "%s" (SymbolTable.Environment.getLookupTable env).Show
            Assert.False true

        
    