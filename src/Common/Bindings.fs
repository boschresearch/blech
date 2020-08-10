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

namespace Blech.Common

module Bindings = 
    open System.Text.RegularExpressions
    open PPrint
    
    [<Literal>]
    let private parameterPattern = "\$[1-9][0-9]*"

    let private getIndex (m: Match) = 
        int <| m.Value.Substring 1

    let getParameterIndices binding =
        let rx = Regex parameterPattern
        let matches = rx.Matches binding
        [ for m in matches -> getIndex m ]

    let replaceParameters binding (actualParams: string list) =
        let replace (m : Match) =
            let i = getIndex m
            match List.tryItem (i-1) actualParams with
            | None -> "$" + string i
            | Some actParam -> actParam

        let evaluator = MatchEvaluator replace
        
        Regex.Replace (binding, parameterPattern, evaluator)

    let toDoc binding = 
        let lines = String.split '\n' binding
        Seq.map txt lines
        |> vsep
        |> align