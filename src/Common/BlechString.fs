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
// Allow '\<newline>' as a line continuation
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

    //[<Literal>]
    //let private Whitespace = "[ \t]*"

    [<Literal>]
    let private Backslash = "\\\\"

    [<Literal>]
    let private LineContinuation = Backslash + Linefeed

    //[<Literal>]
    //let private Quotes = "\""

    [<Literal>]
    let Escape = "\\[abfnrtv\\\'\"]"

    //[<Literal>]
    //let private EscapeSequence = Backslash + "."  // needs RegexOptions.Singleline

    //[<Literal>]
    //let private ValidEscapeSequence = Backslash + "[" + Linefeed + Backslash + "abfnrtvz'x0-9\"]" 

    [<Literal>]
    let private DecimalEscape = Backslash + "[0-9]{1,3}"
    
    //[<Literal>]
    let private HexEscape = Backslash + "x[0-9a-fA-F]{2}"
    
    //[<Literal>]
    //let private ValidHexEscape = Backslash + "x[0-9a-fA-F]{2}"

    [<Literal>]
    let private UnicodeEscape = Backslash + "u\{[0-9a-fA-F]{1,}\}"
   
    [<Literal>]
    let private MaxUnicodeCodePoint = 1114111
   
    

    //let private hasNormalizedEndOfLine str = 
    //    not (Regex.IsMatch(str, @"\r"))
      

    //let isValidEscapeSequence (escSeq: string) =
    //    (Regex ValidEscapeSequence).IsMatch escSeq

    //let isValidHexEscape (hexEsc: string) = 
    //    (Regex ValidHexEscape).IsMatch hexEsc

   
    let decimalEscapeToUtf32 (decEsc: string) : int = 
        let dec = decEsc.Substring(1)
        System.Int32.Parse dec
        
    let isValidDecimalEscape (decEsc: string) =
        let dec = decimalEscapeToUtf32 decEsc
        0 <= dec && dec <= 255

    let hexEscapeToUtf32 (hexEsc: string) : int =
        let hexdigits = hexEsc.Substring 2
        Int32.Parse (hexdigits, System.Globalization.NumberStyles.AllowHexSpecifier)

    /// throws System.OverflowException if hex number is too big
    let unicodeEscapeToUtf32 (unicodeEscape : string) : int32 =
        let hexdigits = unicodeEscape.Substring(3, unicodeEscape.Length - 4)
        System.Int32.Parse(hexdigits, System.Globalization.NumberStyles.HexNumber)
        
    let isValidUnicodeEscape (unicodeEscape : string) =
        try 
            let codepoint = unicodeEscapeToUtf32 unicodeEscape
            0 <= codepoint && codepoint <= MaxUnicodeCodePoint
        with
        | :? System.OverflowException ->
            false

    


    //let unicodeEscapeToUEscape (unicodeEscape: string) =
    //    let codepoint = unicodeEscapeToUtf32 unicodeEscape
    //    if codepoint < int32 System.UInt16.MaxValue then
    //        sprintf "\\u%04x" codepoint // UTF16 representation
    //    else
    //        sprintf "\\U%08x" codepoint // UTF32 representation
            
    //let decimalToOctalEscape (decimal : int) =
    //    assert (0 <= decimal && decimal <= 255)
    //    sprintf "\\%03o" decimal  // octal with 3 digits, leading '0's if necessary

    //let decimalTo3DigitDecimalEscape (decimal : int) =
    //    assert (0 <= decimal && decimal <= 255)
    //    sprintf "\\%03d" decimal // decimal with 3 digits, leading '0's if necessary

    //let decimalToHexEscape (decimal : int) =
    //    assert (0 <= decimal && decimal <= 255)
    //    sprintf "\\x%02x" decimal // hex with 2 digits


    //let decimalToChar (decimal : int) =
    //    assert (0 <= decimal && decimal <= 255)
    //    string decimal

    //let private decimalEscapeTo3DigitDecimalEscape str = 
    //    decimalEscapeToUtf32 str
    //    |> decimalTo3DigitDecimalEscape

    //let private decimalEscapeToOctalEscape str =
    //    decimalEscapeToUtf32 str
    //    |> decimalToOctalEscape 

    //let private decimalEscapeToHexEscape str =
    //    decimalEscapeToUtf32 str
    //    |> decimalToHexEscape 


    //let private decimalEscapesToUnicodeDecimals str =
    //    let mev = MatchEvaluator (fun m -> decimalEscapeTo3DigitDecimalEscape m.Value) 
    //    Regex.Replace(str, DecimalEscape, mev)
    
    //let private decimalEscapesToOctalEscapes str =
    //    let mev = MatchEvaluator (fun m -> decimalEscapeToOctalEscape m.Value) 
    //    Regex.Replace(str, DecimalEscape, mev)
    
    //let private decimalEscapesToHexEscapes str =
    //    let mev = MatchEvaluator (fun m -> decimalEscapeToHexEscape m.Value) 
    //    Regex.Replace(str, DecimalEscape, mev)

    //let private unicodeEscapesToUTFEscapes str = 
    //    let mev = MatchEvaluator (fun m -> unicodeEscapeToUEscape m.Value) 
    //    Regex.Replace(str, UnicodeEscape, mev)
    

    ///

    let escapeToString (esc: string) : string = 
           Regex.Unescape esc

    let decimalEscapeToString (decEsc : string) : string = 
        decimalEscapeToUtf32 decEsc
        |> Char.ConvertFromUtf32

    let hexEscapeToString (hexEsc : string) : string =
        hexEscapeToUtf32 hexEsc
        |> Char.ConvertFromUtf32

    let unicodeEscapeToString (uniEsc : string) : string =
        unicodeEscapeToUtf32 uniEsc
        |> Char.ConvertFromUtf32

    /// This function replaces any end of line sequence by linefeed '\n'.
    let normalizeEndOfLine str =
        Regex.Replace(str, EndOfLine, Linefeed)

    /// This function removes line continuation in strings. 
    /// It assumes, that end of line is normalized to line feed
    let replaceLineContinuations blechString = 
        Regex.Replace(blechString, LineContinuation, "")

    let replaceEscapes blechString = 
        let mev = MatchEvaluator (fun m -> escapeToString m.Value) 
        Regex.Replace(blechString, Escape, mev)
    
    let replaceDecimalEscapes blechString = 
        let mev = MatchEvaluator (fun m -> decimalEscapeToString m.Value) 
        Regex.Replace(blechString, DecimalEscape, mev)
        
    let replaceHexEscapes blechString = 
        let mev = MatchEvaluator (fun m -> hexEscapeToString m.Value) 
        Regex.Replace(blechString, HexEscape, mev)
    
    let replaceUnicodeEscapes blechString = 
        let mev = MatchEvaluator (fun m -> unicodeEscapeToString m.Value) 
        Regex.Replace(blechString, HexEscape, mev)
    
    /// Normalize a string literal from the lexer


    let unescapeStringLiteral blechString =
        // given a normalized Blech string with valid escapes sequences
        replaceLineContinuations blechString
        |> replaceEscapes
        |> replaceDecimalEscapes
        |> replaceHexEscapes
        |> replaceUnicodeEscapes

    //let removeQuotes (str : string) = 
    //    str.Substring (1, str.Length - 2)
        
    //let removeTripleQuotes (str: string) =
    //    str.Substring (3, str.Length - 6)
    

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
    let private Tabs = "[\t]*"
    [<Literal>]
    let private Spaces = "[ ]*"
    [<Literal>]
    let private TabIndentation = "^" + Tabs
    [<Literal>]
    let private Indentation = TabIndentation + Spaces
    [<Literal>]
    let private WhitespaceOnly = "^\s*$"
    
    //// returns true for unbalanced tab indentation and the common indentation
    //let checkMultiLineStringIndentation (mlstr : string) : bool * string =
    //    let tabs line = (Regex TabIndentation).Match(line).Value
    //    let indentation line = (Regex Indentation).Match(line).Value
    //    let lines = mlstr.Split '\n'
    //    // printfn "Lines:%A" lines
    //    match lines with
    //    | [| _ |] -> // first line does not contribute to indentation
    //        (false, NoIndent)
        
    //    | lines ->
    //        let mutable tabIndent = None // the first tab indent determines all other tab indents 
    //        let mutable commonIndent = None
    //        let mutable unbalancedTabIndent = false
            
    //        for line in Array.tail lines do
    //                let indent = indentation line
    //                // printfn ">>%s<<" indent
    //                if (line = Array.last lines) || (line <> indent) then // line contains relevant identation
    //                    // printfn "line:%s;" line
    //                    // check balanced tab identation
    //                    if Option.isNone tabIndent then // init tab indentation 
    //                        tabIndent <- Some <| tabs line
    //                    elif not (tabs line = Option.get tabIndent) then
    //                        unbalancedTabIndent <- true
                        
    //                    // determine common identation
    //                    if Option.isNone commonIndent then // init commonIdent
    //                        printfn "init ident:>>%s<<" indent
    //                        commonIndent <- Some indent
    //                    else
    //                        let ci = Option.get commonIndent
    //                        if ci.StartsWith indent then
    //                            commonIndent <- Some indent
    //                        elif line.StartsWith ci then
    //                            ()
    //                        else
    //                            commonIndent <- Some ""
            
    //        (unbalancedTabIndent, Option.defaultValue NoIndent commonIndent)

    let isWhitespaceLine line = 
        Regex.IsMatch(line, WhitespaceOnly)
 
    let isEmptyLine line = 
        String.Empty = line

    //let getExtraWhitespaceLength line =
    //    Regex.Match(line, WhitespaceOnly).Length

    let getTabIndentation line = 
        Regex.Match(line, TabIndentation).Length

    let getIndentation line = 
        Regex.Match(line, Indentation).Length

    let findUnbalancedTabIndentations (lines: string seq) =
        let mutable tabIndent = None
        let unbalancedTabIndents = 
            seq { for i, line in Seq.indexed <| Seq.tail lines do  // The first line cannot contain tabs due to the lexer
                    if not (isEmptyLine line) then // a empty line is always balanced
                        let lineTabIndent = getTabIndentation line
                        if Option.isNone <| tabIndent then
                            tabIndent <- Some (i, lineTabIndent) // the first tab indentation defines the standard 
                            // yield i, None
                        elif lineTabIndent <> snd (Option.get tabIndent) then
                            // yield i, None
                        //else
                            yield i, lineTabIndent }
        (tabIndent, unbalancedTabIndents)

    //let findExtraWhitespace (lines : string seq) =
    //    seq { for i, line in Seq.indexed lines do
    //            if i > 1 && i = Seq.length lines - 1 then 
    //                // the last of 2 or more lines may contain extra whitespace
    //                yield None
    //            else
    //                let wsLen = getExtraWhitespaceLength line 
    //                if wsLen = 0 then
    //                    yield None
    //                else
    //                    yield Some wsLen }

    // assumes balanced tab indentation and no extra whitespace in empty lines
    let getCommonIndentation (lines: string seq) = 
        let mutable commonIndent = None
        for i, line in Seq.indexed lines do    
            if i > 0 then                               // the first line is not relevant
                if i = Seq.length lines - 1 ||          // the last line is always relevant
                   not (isWhitespaceLine line)  then    // whitespace lines are not relevant
                    let indent = getIndentation line
                    if Option.isNone commonIndent then  // first defining indentation
                        commonIndent <- Some indent
                    elif indent < Option.get commonIndent then
                        commonIndent <- Some indent
        
        Option.defaultValue 0 commonIndent

    let tabIndentationRange (mlsRange : Range.range) (line, tabs) =
        let l = mlsRange.StartLine + line
        Range.range (mlsRange.FileIndex, l, 0, l, tabs)

    let splitMultiLineString (mlstr: string) =
        mlstr.Split Linefeed

    let checkMultiLineString (mlstr: string) =
        normalizeEndOfLine mlstr
        |> splitMultiLineString
        |> findUnbalancedTabIndentations


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
    
    let dedentLine (line : string) n = 
        try
            line.Substring n
        with
        | :? System.ArgumentOutOfRangeException -> 
            String.Empty

    let dedentLines (lines: string seq) = 
        let n = getCommonIndentation lines
        seq { for i, line in Seq.indexed lines do
                if i = 0 then // first line 
                    yield line
                else 
                    yield dedentLine line n }

    let private dedentMultiLineString (mlstr : string) =
        String.split Linefeed mlstr
        |> dedentLines
        |> String.concat Linefeed

    let private removeEmptyFirstLine mlstr = 
        Regex.Replace(mlstr, "^" + Linefeed, String.Empty)

    /// Normalize a triple-quoted ("""...""") string literal from the lexer
    //let normalizeTripleQuotedString str =
    //    normalizeEndOfLine str
    //    |> dedentTripleQuotedString
    //    |> stripNewlineAfterTripleQuotes

    /// Normalize a multi-line string literal from the lexer
    let normalizeMultiLineString str =
        normalizeEndOfLine str
        |> dedentMultiLineString
        |> removeEmptyFirstLine

    ///// Normalize a single-quoted ("...") string literal from the lexer
    //let normalizeSingleQuotedString str =
    //    normalizeEndOfLine str
    
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

        