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
    
    // ----
    // Regular expression patterns
    // ----

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

    [<Literal>]
    let private EscapeSequence = Backslash + "."  // needs RegexOptions.Singleline

    [<Literal>]
    let private ValidEscapeSequence = Backslash + "[" + Linefeed + Backslash + "abfnrtvz'x0-9\"]" 

    [<Literal>]
    let private DecimalEscape = Backslash + "[0-9]{1,3}"
    
    [<Literal>]
    let private HexEscape = Backslash + "x[^\"\n]{0,2}"
    
    [<Literal>]
    let private ValidHexEscape = Backslash + "x[0-9a-fA-F]{2}"

    [<Literal>]
    let private UnicodeEscape = Backslash + "u\{[0-9a-fA-F]{1,}\}"
   
    [<Literal>]
    let private MaxUnicodeCodePoint = 1114111
   
    

    let private hasNormalizedEndOfLine str = 
        not (Regex.IsMatch(str, @"\r"))
      

    let isValidEscapeSequence (escSeq: string) =
        (Regex ValidEscapeSequence).IsMatch escSeq

    let isValidHexEscape (hexEsc: string) = 
        (Regex ValidHexEscape).IsMatch hexEsc

    let decimalEscapeToInt (decEsc: string) : int = 
        let dec = decEsc.Substring(1)
        System.Int32.Parse dec
        
    let isValidDecimalEscape (decEsc: string) =
        let dec = decimalEscapeToInt decEsc
        0 <= dec && dec <= 255

    let isValidUnicodeEscape (unicodeEscape: string) =
        let hexdigits = unicodeEscape.Substring(3, unicodeEscape.Length - 4)
        let codepoint = System.Numerics.BigInteger.Parse(hexdigits, System.Globalization.NumberStyles.HexNumber)
        0I <= codepoint && codepoint <= System.Numerics.BigInteger MaxUnicodeCodePoint

    let decimalToOctalEscape (decimal : int) =
        assert (0 <= decimal && decimal <= 255)
        sprintf "\\%03o" decimal  // octal with 3 digits, leading '0's if necessary

    let decimalTo3DigitDecimalEscape (decimal : int) =
        assert (0 <= decimal && decimal <= 255)
        sprintf "\\%03d" decimal // decimal with 3 digits, leading '0's if necessary

    let decimalToHexEscape (decimal : int) =
        assert (0 <= decimal && decimal <= 255)
        sprintf "\\x%02x" decimal // hex with 2 digits


    let decimalToChar (decimal : int) =
        assert (0 <= decimal && decimal <= 255)
        string decimal

    
    let private decimalEscapeTo3DigitDecimalEscape str = 
        decimalEscapeToInt str
        |> decimalTo3DigitDecimalEscape

    let private decimalEscapeToOctalEscape str =
        decimalEscapeToInt str
        |> decimalToOctalEscape 

    let private decimalEscapeToHexEscape str =
        decimalEscapeToInt str
        |> decimalToHexEscape 


    let private decimalEscapesToUnicodeDecimals str =
        let mev = MatchEvaluator (fun m -> decimalEscapeTo3DigitDecimalEscape m.Value) 
        Regex.Replace(str, DecimalEscape, mev)
    
    let private decimalEscapesToOctalEscapes str =
        let mev = MatchEvaluator (fun m -> decimalEscapeToOctalEscape m.Value) 
        Regex.Replace(str, DecimalEscape, mev)
    
    let private decimalEscapesToHexEscapes str =
        let mev = MatchEvaluator (fun m -> decimalEscapeToHexEscape m.Value) 
        Regex.Replace(str, DecimalEscape, mev)



    
    /// Normalize a string literal from the lexer

    /// This function replaces any end of line sequence by linefeed '\n'.
    let normalizeEndOfLine str =
        Regex.Replace(str, EndOfLine, "\n")

    let removeLineContinuations str = 
        Regex.Replace(str, Backslash + Linefeed, "")

    let unescapeStringLiteral str =
        // given a normalized Blech string with valid escapes sequences
        removeLineContinuations str
        // |> decimalEscapesToOctalEscapes   // both are possible
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

    //let getInvalidEscapeSequences str : seq<Match> = 
    //    Regex.Matches (str, EscapeSequence, RegexOptions.Singleline)
    //    |> Seq.filter (fun m -> not (isValidEscapeSequence m.Value))

    //let getInvalidHexEscapes str: seq<Match> =
    //    Regex.Matches (str, HexEscape)
    //    |> Seq.filter (fun m -> not (isValidHexEscape m.Value))

    //let getInvalidDecimalEscapes str : seq<Match> =
    //    str 
    //    |> (Regex DecimalEscape).Matches
    //    |> Seq.filter (fun m -> not (isValidDecimalEscape m.Value))
        
    //let getInvalidUnicodeEscapes str : seq<Match> =
    //    str 
    //    |> (Regex UnicodeEscape).Matches
    //    |> Seq.filter (fun m -> not (isValidUnicodeEscape m.Value))

    // ---
    // Functions for normalizing multi-line string literals
    // the public functions normalizeTripleQuotedStr expect a raw triple-quoted string with normalized end of line sequence
    // ---

    
    [<Literal>]
    let private TripleQuotes = Quotes + Quotes + Quotes

    
    
    // Asserts that the line starting with """ must is excluded
    
    [<Literal>]
    let private NoIndent = ""
    [<Literal>]
    let private Tabs = "[\t]*"
    [<Literal>]
    let private Spaces = "[ ]*"
    [<Literal>]
    let private TabIndentation = "^" + Tabs
    [<Literal>]
    let private Indentation = TabIndentation + Spaces
    
    // returns true for unbalanced tab indentation and the common indentation
    let checkMultiLineStringIndentation (mlstr : string) : bool * string =
        let tabs line = (Regex TabIndentation).Match(line).Value
        let indentation line = (Regex Indentation).Match(line).Value
        let lines = mlstr.Split '\n'
        // printfn "Lines:%A" lines
        match lines with
        | [| _ |] -> // first line does not contribute to indentation
            (false, NoIndent)
        
        | lines ->
            let mutable tabIndent = None // the first tab indent determines all other tab indents 
            let mutable commonIndent = None
            let mutable unbalancedTabIndent = false
            
            for line in Array.tail lines do
                    let indent = indentation line
                    // printfn ">>%s<<" indent
                    if (line = Array.last lines) || (line <> indent) then // line contains relevant identation
                        // printfn "line:%s;" line
                        // check balanced tab identation
                        if Option.isNone tabIndent then // init tab indentation 
                            tabIndent <- Some <| tabs line
                        elif not (tabs line = Option.get tabIndent) then
                            unbalancedTabIndent <- true
                        
                        // determine common identation
                        if Option.isNone commonIndent then // init commonIdent
                            printfn "init ident:>>%s<<" indent
                            commonIndent <- Some indent
                        else
                            let ci = Option.get commonIndent
                            if ci.StartsWith indent then
                                commonIndent <- Some indent
                            elif line.StartsWith ci then
                                ()
                            else
                                commonIndent <- Some ""
            
            (unbalancedTabIndent, Option.defaultValue NoIndent commonIndent)
 
 
    // Asserts that the line starting with """ must is excluded
    //let private longestCommonStartingSequence (lines: string list) = 
    //    match lines with
    //    | fst :: tail ->
    //        let startingSequence line =
    //            (Regex Indentation).Match(line).Value
    //        let mutable lcss = startingSequence fst
    //        for line in tail do
    //            let startSeq = startingSequence line 
    //            if not (line = startSeq) then // line actually contains text
    //                if lcss.StartsWith startSeq then
    //                    lcss <- startSeq
    //                elif line.StartsWith lcss then
    //                    ()
    //                else
    //                    lcss <- ""
    //            else
    //                ()
    //        lcss
    //    | _ -> 
    //        ""
    

    let private dedentMultiLineString indentation (mlstr : string) =
        // let lines = String.split '\n' tqstr 
        // let lcss = longestCommonStartingSequence (List.tail lines)
        // Regex.Replace(mlstr, "\n" + indentation, "\n")
        // TODO: handle empty lines correctly, fjg 20.08.20
        printfn "indentation:>%s<" indentation
        mlstr.Replace("\n" + indentation, "\n")

    let private removeEmptyFirstLine mlstr = 
        Regex.Replace(mlstr, "^" + Linefeed, "")

    /// Normalize a triple-quoted ("""...""") string literal from the lexer
    //let normalizeTripleQuotedString str =
    //    normalizeEndOfLine str
    //    |> dedentTripleQuotedString
    //    |> stripNewlineAfterTripleQuotes

    /// Normalize a triple-quoted ("""...""") string literal from the lexer
    let normalizeMultiLineString indentation str =
        normalizeEndOfLine str
        |> dedentMultiLineString indentation
        |> removeEmptyFirstLine

    /// Normalize a single-quoted ("...") string literal from the lexer
    let normalizeSingleQuotedString str =
        normalizeEndOfLine str
    
    /// Normalize a single-line ("...") string literal from the lexer
    let normalizeSingleLineString str =
        normalizeEndOfLine str
    

    // --
    // Functions for calculating error ranges
    // expects a raw string with normalized end of line
    // --

    //let getMatchRange (str: String, rng: Range.range) (m : Match) =
    //    let mutable startPos = (0, 0)
    //    let mutable endPos = (0, 0)
    //    let mutable line = rng.StartLine
    //    let mutable column = rng.StartColumn
    //    let fstIdx = m.Index
    //    let lstIdx = m.Index + m.Length - 1
    //    for i in 0 .. lstIdx do
            
    //        if i = fstIdx then
    //            startPos <- (line, column)
    //        elif i = lstIdx then
    //            endPos <- (line, column)
    //        else 
    //            ()
            
    //        if str.[i] = '\n' then
    //            line <- line + 1
    //            column <- 1
    //        else
    //            column <- column + 1

    //    Range.range(rng.FileIndex, 
    //                fst startPos, snd startPos, 
    //                fst endPos, snd endPos)

        