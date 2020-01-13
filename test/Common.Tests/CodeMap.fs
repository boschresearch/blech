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

// Unit Test -----------------------------------------------------------
namespace Blech.Common.Tests

open NUnit.Framework
open System.IO
open Blech.Common.CodeMap // system under test

[<TestFixture>]
type CodeMapTests () =
    
    let mySource = Path.Combine(__SOURCE_DIRECTORY__, __SOURCE_FILE__)

    [<Test>]
    member t.``test second line`` () =
        printfn "Source path: %s" mySource 
        let nameSpaceLine = lineOfFile mySource 18
        printfn "Namespace line: %s" nameSpaceLine
        let cond = nameSpaceLine = "namespace Blech.Common.Tests"
        Assert.True cond
    
    [<Test>]
    member t.``test last line``() =
        let lastLine = lineCountOfFile mySource |> lineOfFile mySource
        printfn "Last line: %s" lastLine
        let cond = lastLine = "        Assert.True cond"
        Assert.True cond
