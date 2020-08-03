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
    open System
    open System.Text.RegularExpressions
    
    [<Literal>]
    let private EndOfLine = "(\n\r|\r\n|\r|\n)"

    [<Literal>]
    let private Newline = "\n"

    [<Literal>]
    let private Whitespace = "[ \a\b\f\t\v]*"

    [<Literal>]
    let private Backslash = "\\\\"

    [<Literal>]
    let private Quotes = "\""


    //[<Literal>]
    //let private BackSlashNewlineWhitespace = "\\\n" + Whitespace

    //[<Literal>]
    //let private ImmediateNewline = "^\n"

    [<Literal>]
    let private TwoQuotes = Quotes + Quotes

    [<Literal>]
    let private BackslashDoubleQuotes = Backslash + Quotes


    [<Literal>]
    let invalidCharacterEscape = "\\\\[^abfnrtvz\\\"'x0-9]"
    
    [<Literal>]
    let decimalEscape = "\\\\[0-9]{1,3}"
    
    [<Literal>]
    let invalidHexEscape = "\\\\x([^ 0-9 a-f A-F].|.[^ 0-9 a-f A-F])"
    

    let private hasNormalizedEndOfLine str = 
        not (Regex.IsMatch(str, @"\r"))
        
    let normalizeEndOfLine str =
        Regex.Replace(str, EndOfLine, "\n")

    //let removeBackslashNewlineWhitespace str =
    //    assert hasNormalizedEndOfLine str
    //    Regex.Replace(str, BackSlashNewlineWhitespace, "")

    //let removeBackslashWhitespace str =
    //    assert hasNormalizedEndOfLine str

    //let removeImmediateNewline str =
    //    assert hasNormalizedEndOfLine str
    //    Regex.Replace(str, ImmediateNewline, "")
    
    
    let decimalEscapeToInt (decEsc: string) : int = 
        let dec = decEsc.Substring(1)
        System.Int32.Parse dec
        
    let private isValidDecimalEscape (decEsc: string) =
        let dec = decimalEscapeToInt decEsc
        0 <= dec && dec <= 255

    let decimalToOctalEscape (decimal : int) =
        assert (0 <= decimal && decimal <= 255)
        Backslash + sprintf "%03o" decimal  // octal with 3 digits, leading '0's if necessary

    let decimalToUnicodeDecimal (decimal : int) =
        assert (0 <= decimal && decimal <= 255)
        Backslash + sprintf "%03d" decimal // decimal with 3 digits, leading '0's if necessary

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
        Regex.Replace(str, Backslash + Whitespace + Newline, "")

    /// Normalize a verbatim string literal from the lexer
    let normalizeVerbatimStringLiteral str =
        Regex.Replace(str, Quotes + Quotes, Quotes)

    /// Normalize a multiline string literal from the lexer
    let normalizeMultiLineStringLiteral str =
        let ns = normalizeStringLiteral str
        Regex.Replace(ns, Backslash + Quotes, Quotes)

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

    [<Literal>]
    let TripleQuotes = Quotes + "{3}"

    [<Literal>]
    let InvalidOpeningQuotes = "^" + TripleQuotes + ".+" + Newline  // any character after """

    [<Literal>]
    let InvalidClosingQuotes = Whitespace + ".+" + TripleQuotes + "$" // any non-whitespace before """

    [<Literal>]
    let LeadingWhitespace = Newline + "(" + Whitespace + ")" // Leading white space 

    [<Literal>]
    let Indentation = Whitespace + TripleQuotes + "$"  // whitespace before """

    
    //let splitMultilineStringLiteral (str : string) = 
    //    str.Split '\n'
        
    let getInvalidOpeningQuotes multilineStr =
        (Regex InvalidOpeningQuotes).Match multilineStr
        
    let getInvalidClosingQuotes multilineStr=
        (Regex InvalidClosingQuotes).Match multilineStr

    let getMinimalIndentation multilineStr =
        let m = (Regex Indentation).Match multilineStr
        m.Length

    let getInvalidLeadingWhitespace multilineStr =
        let minIndent = getMinimalIndentation multilineStr
        (Regex LeadingWhitespace).Matches multilineStr
        |> Seq.filter (fun m ->  m.Length < minIndent)

    // --
    // Functions for calculating error ranges
    // expects a raw string with normalized end of line
    // --

    // TODO: This is totally wrong: onlyworks for "<str>" without line continuations, fjg. 1.8.2020
    // Differentiate ranges for "..", @".." and """.."""

    let getRelativePositions (str: string) index length =
        // relative positions are zero-based
        let mutable startPos = (0, 0)
        let mutable endPos = (0, 0)
        let mutable line = 0
        let mutable column = 0
        for i in 0 .. String.length str - 1 do
            if str.[i] = '\n' then
               line <- line + 1
               column <- 0
            else
               column <- column + 1
            
            if i = index then
                startPos <- (line, column)
            elif i = index + length - 1 then
                endPos <- (line, column)
            else 
                ()
        (startPos, endPos)


    /// calculates 

    let getMatchRange (str: String, rng: Range.range) (m : Match) =
        let (startLine, startColumn), (endLine, endColumn) = 
            getRelativePositions str m.Index m.Length
        
        Range.range(rng.FileIndex,  
                    rng.StartLine + startLine, rng.StartColumn + startColumn, 
                    rng.StartLine + endLine, rng.StartColumn + endColumn)
