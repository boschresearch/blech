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


    //[<Literal>]
    //let invalidCharacterEscape = "\\\\[^abfnrtvz'x0-9\"\\\n\\\\]"
    
    [<Literal>]
    let EscapeSequence = Backslash + "."  // needs RegexOptions.Singleline
    let ValidEscapeSequence = Backslash + "[" + Linefeed + Backslash + "abfnrtvz'x0-9\"]" 

    [<Literal>]
    let DecimalEscape = Backslash + "[0-9]{1,3}"
    
    [<Literal>]
    let HexEscape = Backslash + "x[^\"\n]{0,2}"
    let ValidHexEscape = Backslash + "x[0-9a-fA-F]{2}"
    

    let private hasNormalizedEndOfLine str = 
        not (Regex.IsMatch(str, @"\r"))
      
    /// This function replaces any end of line sequence by linefeed '\n'.
    let normalizeEndOfLine str =
        Regex.Replace(str, EndOfLine, "\n")


    let isValidEscapeSequence (escSeq: string) =
        (Regex ValidEscapeSequence).IsMatch escSeq

    let isValidHexEscape (hexEsc: string) = 
        (Regex ValidHexEscape).IsMatch hexEsc

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

    let decimalToHexEscape (decimal : int) =
        assert (0 <= decimal && decimal <= 255)
        Backslash + sprintf "x%02x" decimal // decimal with 3 digits, leading '0's if necessary


    let decimalToChar (decimal : int) =
        assert (0 <= decimal && decimal <= 255)
        string decimal

    
    let private decimalEscapeToUnicodeDecimal str = 
        decimalEscapeToInt str
        |> decimalToUnicodeDecimal

    let private decimalEscapeToOctalEscape str =
        decimalEscapeToInt str
        |> decimalToOctalEscape 

    let private decimalEscapeToHexEscape str =
        decimalEscapeToInt str
        |> decimalToHexEscape 


    let private decimalEscapesToUnicodeDecimals str =
        let mev = MatchEvaluator (fun m -> decimalEscapeToUnicodeDecimal m.Value) 
        Regex.Replace(str, DecimalEscape, mev)
    
    let private decimalEscapesToOctalEscapes str =
        let mev = MatchEvaluator (fun m -> decimalEscapeToOctalEscape m.Value) 
        Regex.Replace(str, DecimalEscape, mev)
    
    let private decimalEscapesToHexEscapes str =
        let mev = MatchEvaluator (fun m -> decimalEscapeToHexEscape m.Value) 
        Regex.Replace(str, DecimalEscape, mev)
    
    /// Normalize a string literal from the lexer

    let removeLineContinuations str = 
        Regex.Replace(str, Backslash + Linefeed, "")

    let normalizeSingleQuotedString str =
        normalizeEndOfLine str
    
    let unescapeStringLiteral str =
        // given a normalized Blech string with valid escapes sequences
        removeLineContinuations str
        |> decimalEscapesToHexEscapes
        // Regex.Unescape does the job to replace escape sequences
        |> Regex.Unescape

    let removeQuotes (str : string) = 
        str.Substring (1, str.Length - 2)
        
    let removeTripleQuotes (str: string) =
        str.Substring (3, str.Length - 6)
    
    


    // ---
    // Functions for normalizing string literals
    // all functions expect a string with normalized end of line sequences
    // ---
    

    // ---
    // Functions for checking escape sequences
    // --

    //let getInvalidCharacterEscapes str : seq<Match> = 
    //    seq <| (Regex invalidCharacterEscape).Matches str

    let getInvalidEscapeSequences str : seq<Match> = 
        Regex.Matches (str, EscapeSequence, RegexOptions.Singleline)
        |> Seq.filter (fun m -> not (isValidEscapeSequence m.Value))

    let getInvalidHexEscapes str: seq<Match> =
        Regex.Matches (str, HexEscape)
        |> Seq.filter (fun m -> not (isValidHexEscape m.Value))

    let getInvalidDecimalEscapes str : seq<Match> =
        str 
        |> (Regex DecimalEscape).Matches
        |> Seq.filter (fun m -> not (isValidDecimalEscape m.Value))
        
    // ---
    // Functions for normalizing multi-line string literals
    // the public functions normalizeTripleQuotedStr expect a raw triple-quoted string with normalized end of line sequence
    // ---

    
    [<Literal>]
    let private TripleQuotes = Quotes + Quotes + Quotes

    [<Literal>]
    let private LeadingWhitespace = "^" + Whitespace

    // Asserts that the line starting with """ must is excluded
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
    let normalizeTripleQuotedString str =
        normalizeEndOfLine str
        |> dedentTripleQuotedString
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

        