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
    let bla = '\n'


module BlechString = 
    open System
    open System.Text.RegularExpressions
    
    [<Literal>]
    let private EndOfLine = "(\n\r|\r\n|\r|\n)"

    [<Literal>]
    let private Linefeed = "\n"

    [<Literal>]
    let private Whitespace = "[ \t]*"

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
    let invalidCharacterEscape = "\\\\[^abfnrtvz\\\"'x0-9\n]"
    
    [<Literal>]
    let decimalEscape = "\\\\[0-9]{1,3}"
    
    [<Literal>]
    let invalidHexEscape = "\\\\x([^ 0-9 a-f A-F].|.[^ 0-9 a-f A-F])"
    

    let private hasNormalizedEndOfLine str = 
        not (Regex.IsMatch(str, @"\r"))
      
    /// This function replaces any end of line sequence by linefeed '\n'.
    /// Only for test purposes. Blech normalizes eol sequences in the lexer,
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
        Regex.Replace(str, Backslash + Linefeed, "")


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
    // Functions for normalizing multi-line string literals
    // the public functions normalizeTripleQuotedStr expect a raw triple-quoted string with normalized end of line sequence
    // ---

    
    [<Literal>]
    let private TripleQuotes = Quotes + Quotes + Quotes

    [<Literal>]
    let private LeadingWhitespace = "^" + Whitespace

    // Asserts that the line following """ must is excluded
    let private longestCommonStartingSequence (lines: string list) = 
        match lines with
        | fst :: tail ->
            let startingSequence line =
                (Regex LeadingWhitespace).Match(line).Value
            let mutable lcss = startingSequence fst
            for line in tail do
                let startSeq = startingSequence line 
                if not (line = startSeq) then // line actually contains text
                    if lcss.StartsWith startSeq then
                        lcss <- startSeq
                    elif line.StartsWith lcss then
                        ()
                    else
                        lcss <- ""
                else
                    ()
            lcss
        | _ -> 
            ""
    
    let private dedentTripleQuotedString tqstr =
        let lines = String.split '\n' tqstr 
        let lcss = longestCommonStartingSequence (List.tail lines)
        Regex.Replace(tqstr, "\n" + lcss, "\n")


    let private stripNewlineAfterTripleQuotes tqstr = 
        Regex.Replace(tqstr, "^" + TripleQuotes + Linefeed, TripleQuotes)

    /// Normalize a multiline string literal from the lexer
    /// expects a raw triple-quoted string with normalized end-of-line
    let normalizeTripleQuotedStringLiteral str =
        dedentTripleQuotedString str
        |> stripNewlineAfterTripleQuotes


    // --
    // Functions for calculating error ranges
    // expects a raw string with normalized end of line
    // --


    let getMatchRange (str: String, rng: Range.range) (m : Match) =
        let mutable startPos = (0, 0)
        let mutable endPos = (0, 0)
        let mutable line = rng.StartLine
        let mutable column = rng.StartColumn
        let fstIdx = m.Index
        let lstIdx = m.Index + m.Length - 1
        for i in 0 .. lstIdx do
            
            if i = fstIdx then
                startPos <- (line, column)
            elif i = lstIdx then
                endPos <- (line, column)
            else 
                ()
            
            if str.[i] = '\n' then
                line <- line + 1
                column <- 1
            else
                column <- column + 1

        Range.range(rng.FileIndex, 
                    fst startPos, snd startPos, 
                    fst endPos, snd endPos)

        