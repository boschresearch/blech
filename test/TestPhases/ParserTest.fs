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

module ParserTests

open Blech.Common

open NUnit.Framework

[<TestFixture>]
type Test() =

    /// load test cases for parseValidInputs test
    static member validFiles = 
        TestFiles.validFiles TestFiles.Parser
        
    /// run parseValidInputs
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "validFiles")>]
    member __.ParseValidFiles (implOrIface, moduleName, filePath) =
        let logger = Diagnostics.Logger.create ()
        let ast = Blech.Frontend.ParsePkg.parseModuleFromFile logger implOrIface moduleName filePath
        if Result.isError ast then
            Diagnostics.Emitter.printDiagnostics logger
        Assert.True (Result.isOk ast)
        //printfn "%s" (Blech.Frontend.PrettyPrint.pprint (Blech.Frontend.AST.ASTNode.Package result))
        //Assert.IsInstanceOf(typeof<Blech.Frontend.AST.Package>, result)

    /// load test cases for parseInvalidInputs test
    static member invalidFiles =
        TestFiles.invalidFiles TestFiles.Parser
        
    /// run parseInvalidInputs
    [<Test>]
    [<TestCaseSource(typedefof<Test>, "invalidFiles")>]
    member __.ParseInvalidInputs (implOrIface, moduleName, filePath) =
        try
            let logger = Diagnostics.Logger.create ()
            let ast = Blech.Frontend.ParsePkg.parseModuleFromFile logger implOrIface moduleName filePath
            if Result.isError ast then
                Diagnostics.Emitter.printDiagnostics logger
            Assert.False (Result.isOk ast)
        with
            | FSharp.Text.Parsing.RecoverableParseError -> Assert.True true //TODO: this does not work, RecoverableParseError is not caught here (fg, 12.01.17)
        //Assert.Throws<Blech.Core.Console.FatalError> (fun () -> Blech.Frontend.ParsePkg.parseFile filePath |> ignore)
        

    