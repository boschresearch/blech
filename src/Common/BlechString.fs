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


// Blech strings follow Lua for escape codes https://www.lua.org/manual/5.4/manual.html#3.1
// Allow '\z' like in Lua and '\<newline>' like in F#
// All end of line sequences should be normalized first

module BlechChar = 
    let private Bla = '\n'


module BlechString = 

    open System.Text.RegularExpressions

    [<Literal>]
    let private Whitespace = @"[ \a\b\f\t\v]*"

    [<Literal>]
    let private EndOfLine = @"(\n\r|\r\n|\r|\n)"

    [<Literal>]
    let private BackslashZeeWhitespace = @"\\z[ \a\b\f\t\v\n]*"

    [<Literal>]
    let private BackSlashNewlineWhitespace = @"\\\n" + Whitespace

    [<Literal>]
    let private ImmediateNewline = @"^\n"

    [<Literal>]
    let private TwoDoubleQuotes = "\"\""

    [<Literal>]
    let invalidCharacterEscape = @"\\[^abfnrtvz\\""'0-9x\n\r]"
    
    [<Literal>]
    let decimalEscape = @"\\[0-9]{1,3}"
    
    [<Literal>]
    let invalidHexEscape = @"\\x([^ 0-9 a-f A-F].|.[^ 0-9 a-f A-F])"
    

    let private hasNormalizedEndOfLine str = 
        not (Regex.IsMatch(str, @"\r"))
        
    let normalizeEndOfLine str =
        Regex.Replace(str, EndOfLine, "\n")

    let removeBackslashNewlineWhitespace str =
        assert hasNormalizedEndOfLine str
        Regex.Replace(str, BackSlashNewlineWhitespace, "")

    let removeBackslashZeeWhitespace str =
        assert hasNormalizedEndOfLine str
        Regex.Replace(str, BackslashZeeWhitespace, "")

    let removeImmediateNewline str =
        assert hasNormalizedEndOfLine str
        Regex.Replace(str, ImmediateNewline, "")


    
    
    let decimalEscapeToInt (decEsc: string) : int = 
        let dec = decEsc.Substring(1)
        System.Int32.Parse dec
        
    let private isValidDecimalEscape (decEsc: string) =
        let dec = decimalEscapeToInt decEsc
        0 <= dec && dec <= 255

    let decimalToOctalEscape (decimal : int) =
        assert (0 <= decimal && decimal <= 255)
        "\\" + sprintf "%03o" decimal  // octal with 3 digits, leading '0's if necessary

    let decimalToUnicodeDecimal (decimal : int) =
        assert (0 <= decimal && decimal <= 255)
        "\\" + sprintf "%03d" decimal // decimal with 3 digits, leading '0's if necessary

    let decimalToChar (decimal : int) =
        assert (0 <= decimal && decimal <= 255)
        string decimal

    

    let private decimalEscapeToUnicodeDecimal str = 
        decimalEscapeToInt str
        |> decimalToUnicodeDecimal


    let private decimalEscapesToUnicodeDecimals str =
        let mev = MatchEvaluator (fun m -> decimalEscapeToUnicodeDecimal m.Value) 
        Regex.Replace(str, decimalEscape, mev)
    
    
    let unescapeNormalizedStringLiteral str =
        // given a normalized Blech string with valid escapes sequences
        decimalEscapesToUnicodeDecimals str
        // Regex.Unescape does the job
        |> Regex.Unescape

    // ---
    // Functions for normalizing string literals
    // all functions expect a string with normalized end of line sequences
    // ---
    
    /// Normalize a string literal from the lexer
    let normalizeStringLiteral str = 
        removeBackslashNewlineWhitespace str


    /// Normalize a verbatim string literal from the lexer
    let normalizeVerbatimStringLiteral str =
        let ns = normalizeStringLiteral str
        Regex.Replace(ns, "\"\"", "\"")

    /// Normalize a multiline string literal from the lexer
    let normalizeMultiLineStringLiteral str =
        let ns = normalizeStringLiteral str
        Regex.Replace(ns, "\\\"", "\"")

    // ---
    // Functions for checking escape sequences
    // --

    let getInvalidCharacterEscapes str : seq<Match> = 
        seq <| (Regex invalidCharacterEscape).Matches str

    let getInvalidHexEscapes str: seq<Match> =
        seq <| (Regex invalidHexEscape).Matches str

    let getInvalidDecimalEscapes str : seq<Match> =
        str 
        |> (Regex decimalEscape).Matches
        |> Seq.filter (fun m -> not (isValidDecimalEscape m.Value))
        
    // ---
    // Functions for checking multi-line string literals
    // all expect a string with normalized end of line sequence
    // ---

    type Lines = string []

    [<Literal>]
    let InvalidOpeningQuotes = "^.+\n"  // any character after """

    [<Literal>]
    let InvalidClosingQuotes = "\n" + Whitespace + ".+$" // any non-whitespace before """

    [<Literal>]
    let LeadingWhitespace = "\n" + Whitespace // Leading white space 

    [<Literal>]
    let BeforeClosingQuotes = LeadingWhitespace + "$"  // whitespace before """

    
    let splitMultilineStringLiteral (str : string) = 
        str.Split '\n'
        
    let getInvalidOpeningQuotes multilineStr =
        (Regex InvalidOpeningQuotes).Match multilineStr
        
    let getInvalidClosingQuotes multilineStr=
        (Regex InvalidClosingQuotes).Match multilineStr

    let getMinimalIndentation multilineStr =
        let m = (Regex BeforeClosingQuotes).Match multilineStr
        m.Length

    let getInvalidLeadingWhitespace multilineStr =
        let minIndent = getMinimalIndentation multilineStr
        (Regex LeadingWhitespace).Matches multilineStr
        |> Seq.filter (fun m ->  m.Length < minIndent)

    // --
    // Functions for calculating error ranges
    // --

    // TODO: This is totally wrong: onlyworks for "<str>" without line continuation, fjg. 1.8.2020
    // Differentiate ranges for "..", @".." and """.."""
    let getEscapeRange (stringRng : Range.range) (m : Match) = 
        Range.range(stringRng.FileIndex,  
                    stringRng.StartLine, stringRng.StartColumn + m.Index + 1, 
                    stringRng.StartLine, stringRng.StartColumn + m.Index + m.Length)
