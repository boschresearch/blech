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

module TestFiles

open System.IO
open NUnit.Framework
open Blech.Common

type Phase =
    | Parser 
    | Namecheck
    | Typechecker
    | Causality
    member p.Directory =
        match p with
        | Parser -> "parser"
        | Namecheck -> "namecheck"
        | Typechecker -> "typechecker"
        | Causality -> "causality"

type Validity = 
    | Valid
    | Invalid
    member v.Directory = 
        match v with
        | Valid -> "valid"
        | Invalid -> "invalid"


let private modulesAndFiles (phase: Phase) (validity: Validity) =
    let where = Path.Combine(__SOURCE_DIRECTORY__, phase.Directory, validity.Directory)
    let testCaseNameFrom moduleName =
        sprintf "%s/%s: %s" phase.Directory validity.Directory (SearchPath.moduleNameToString moduleName)
    let mkTestCaseData file = 
        let modName = 
            printfn "file name: '%s'" file
            match SearchPath.getModuleName where None file with
            | Ok ids -> ids
            | Error wrongIds -> wrongIds //failwith (sprintf "illegal filename '%A'" wrongIds)
        printfn "module name: '%s'" <| SearchPath.moduleNameToString modName
        let testName = testCaseNameFrom modName
        let loadWhat = Option.get (CompilationUnit.loadWhat file) 
        TestCaseData(loadWhat, modName, file).SetName(testName)    
    let files = 
        Directory.EnumerateFiles where
    
    Seq.filter (fun f -> SearchPath.isImplementation f || SearchPath.isInterface f) files
    |> Seq.map mkTestCaseData

/// Returns a sequence of TestCaseData formed from pairs: filepath * modulename, for invalid source files 
let invalidFiles phase =
    modulesAndFiles phase Invalid

/// Returns a sequence of TestCaseData formed from pairs: filepath * modulename, for valid source files
let validFiles phase =
    modulesAndFiles phase Valid

