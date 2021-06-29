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
open Blech.Common.TranslationUnitPath

type Phase =
    | Parser 
    | Namecheck
    | OpaqueInference
    | ExportInference
    | Typechecker
    | Causality
    | ImportChecker
    member p.Directory =
        match p with
        | Parser -> "parser"
        | Namecheck -> "namecheck"
        | OpaqueInference -> "opaqueinference"
        | ExportInference -> "exportinference"
        | Typechecker -> "typechecker"
        | Causality -> "causality"
        | ImportChecker -> "importchecking"

type Validity = 
    | Valid
    | Invalid
    member v.Directory = 
        match v with
        | Valid -> "valid"
        | Invalid -> "invalid"


let private modulesAndFiles (phase: Phase) (validity: Validity) =
    let fileDirectory = Path.Combine(__SOURCE_DIRECTORY__, phase.Directory, validity.Directory)
    let fakeProjectDir = Path.Combine(__SOURCE_DIRECTORY__, phase.Directory)
    let testCaseNameFrom moduleName =
        sprintf "%s/%s: %s" phase.Directory validity.Directory (moduleName.ToString())
    let mkTestCaseData file = 
        let modName = 
            // printfn "file name: '%s'" file
            match tryMakeTranslationUnitPath file fakeProjectDir None with
            | Ok fp -> fp
            | Error wrongIds -> failwith (sprintf "illegal filename '%A'" wrongIds)
        // printfn "module name: '%s'" <| modName.ToString()
        let testName = testCaseNameFrom modName
        let loadWhat = Option.get (CompilationUnit.loadWhat file) 
        TestCaseData(loadWhat, modName, file).SetName(testName)    
    let files = 
        Directory.EnumerateFiles fileDirectory
    
    Seq.filter (fun f -> isImplementation f || isInterface f) files
    |> Seq.map mkTestCaseData

/// Returns a sequence of TestCaseData formed from pairs: filepath * modulename, for invalid source files 
let invalidFiles phase =
    modulesAndFiles phase Invalid

/// Returns a sequence of TestCaseData formed from pairs: filepath * modulename, for valid source files
let validFiles phase =
    modulesAndFiles phase Valid
  

let makeCliContext phasedir inputfile : Arguments.BlechCOptions =
    let projectDir = System.IO.Path.Combine(__SOURCE_DIRECTORY__, phasedir)
    let blechPath = System.IO.Path.Combine(__SOURCE_DIRECTORY__, "boxes")
    { Arguments.BlechCOptions.Default with inputFile = inputfile
                                           projectDir = projectDir
                                           blechPath = blechPath}


let printImportDiagnostics (translatedUnit, importLogger) = 
    printfn "Imported Module: %s \n" <| string translatedUnit
    Diagnostics.Emitter.printDiagnostics importLogger