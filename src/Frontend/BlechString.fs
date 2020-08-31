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

module BlechString = 
    open System.Text.RegularExpressions
    
    let invalidEscapeSequence = Regex @"\\[^ abfnrtv\\""' 0-9 x]"
    
    let decimalEscape = Regex @"\\[0-9]{1,3}"
    
    let invalidHexEscape = Regex @"\\x([^ 0-9 a-f A-F].|.[^ 0-9 a-f A-F])"
    

    let decimalEscapeToInt (decEsc: string) : int = 
        let dec = decEsc.Substring(1)
        System.Int32.Parse dec
        
    let isValidDecimalEscape (decEsc: string) =
        let dec = decimalEscapeToInt decEsc
        (0 <= dec) && (dec <= 255)

    let decimalToOctalEscape (decimal : int) =
        assert (0 <= decimal && decimal <= 255)
        "\\" + sprintf "%03o" decimal  // octal with 3 digits