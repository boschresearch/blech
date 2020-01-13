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

open System

let replace (path: string) = path.Replace('/', IO.Path.DirectorySeparatorChar)

let dirs = [ 
    replace "blechc/tmp"
    replace "blechc/tmp/88problemsbutastructaintone"
    replace "blechc/tmp/blechAccess" ]

let getTraceFilesInDir dir = 
    IO.Directory.GetFiles dir
    |> Array.filter (fun f -> f.EndsWith ".test.json") 

let updateSpecFile (traceFile : String) = 
    let specFile = traceFile.Replace("tmp", "codegeneration")
                            .Replace(".test.", ".spec.")
    
    // read the contents line by line
    // if we read via ReadAllText then later on we would find differences
    // between files with \n and \r\n which we don't want
    let specContents = IO.File.ReadAllLines specFile
    let testContents = IO.File.ReadAllLines traceFile

    // let's update only if contents differ
    // if they are the same, let them be
    // this keeps a clean file version history without commited changes with an empty diff
    if specContents <> testContents then
        //printfn "from: \n%s\n to: \n%s\n" traceFile specFile
        IO.File.Delete specFile
        IO.File.Copy(sourceFileName = traceFile, 
                     destFileName = specFile, 
                     overwrite = true) 


dirs
|> List.iter (
    getTraceFilesInDir
    >> Array.iter updateSpecFile
    ) 