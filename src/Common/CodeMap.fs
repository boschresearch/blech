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

module Blech.Common.CodeMap
    
open System.Collections.Generic

type private CodeMap() = 
    let fileToLinesTable = new Dictionary<string, string[]>()  // Ln i is lines.[i-1], lines start with index 0

    member cm.FileToLines f =
        let ok, lines = fileToLinesTable.TryGetValue f
        if ok then
            lines
        else
            let lines = System.IO.File.ReadAllLines f
            do fileToLinesTable.Add(f, lines)
            lines
        
    member cm.FileToLine f n =
        let ls = cm.FileToLines f
        ls.[n-1]

    member cm.LineCountOfFile f = 
        let lines = cm.FileToLines f
        lines.Length

// +++ GLOBAL MUTABLE STATE +++
let private codeMap = new CodeMap()

/// Get alle lines from file, and cache them in codeMap
let linesOfFile f = codeMap.FileToLines(f)

/// Get a single line form file, the lines are cached in codeMap
let lineOfFile f n = codeMap.FileToLine f n

let lineCountOfFile f = codeMap.LineCountOfFile f
