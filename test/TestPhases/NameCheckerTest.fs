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


let runNameChecking implOrIface moduleName filePath =
    let cliContext = Arguments.BlechCOptions.Default
    let logger = Diagnostics.Logger.create ()
    let options = 
        { Arguments.BlechCOptions.Default 
            with inputFile = filePath
                 sourcePath = System.IO.Path.Combine(__SOURCE_DIRECTORY__, TestFiles.Namecheck.Directory) }
    let pkgCtx = CompilationUnit.Context.Make options (Blech.Compiler.Main.loader options)

    let ast = ParsePkg.parseModuleFromFile logger implOrIface moduleName filePath
    Assert.True (Result.isOk ast)
    
    let importsRes =
        ast
        |> Result.bind (Blech.Compiler.Main.runImportCompilation pkgCtx logger CompilationUnit.ImportChain.Empty moduleName filePath)
                    
    match ast, importsRes with
    | Ok ast, Ok imports -> 
        let lookupTables = imports.GetLookupTables
        let exportScopes = imports.GetExportScopes
        Blech.Compiler.Main.runNameResolution logger moduleName filePath lookupTables exportScopes ast
    | Error errs, _ 
    | _, Error errs ->
        printfn "Did not expect to find errors during parsing or in imported files!\n" 
        Diagnostics.Emitter.printDiagnostics errs
        Error errs
    
[<TestFixture>]
type Test() =

    /// load test cases for nameCheckValidFiles test
    static member validFiles =
        TestFiles.validFiles TestFiles.Namecheck
        
    /// run nameCheckValidFiles
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member x.NameCheckValidFiles (implOrIface, moduleName, filePath) =
        
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
    member x.NameCheckInvalidInputs (implOrIface, moduleName, filePath) =
        match runNameChecking implOrIface moduleName filePath with
        | Error logger ->
            Diagnostics.Emitter.printDiagnostics logger
            Assert.True true
        | Ok env ->
            // printfn "%s" (SymbolTable.Environment.getLookupTable env).Show
            Assert.False true

        
    