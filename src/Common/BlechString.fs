// Copyright (c) 2020 - for information on the respective copyright owner
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

type BlechString = byte [] // a blech string is an array of bytes

module BlechString = 
    open System
    open System.Text.RegularExpressions
    

    // ----
    // Regular expression patterns
    // ----
    

    [<Literal>]
    let EndOfLine = "(\n\r|\r\n|\r|\n)"
    
    [<Literal>]
    let Linefeed = "\n"

    [<Literal>]
    let private Backslash = "\\\\"

    [<Literal>]
    let private LineContinuation = Backslash + Linefeed

    [<Literal>]
    let private MaxUnicodeCodePoint = 1114111 // U+10ffff
   
    
    let private decimalEscapeToByte (decEsc: string) : byte = 
        let dec = decEsc.Substring(1)
        Byte.Parse dec

        
    let isValidDecimalEscape (decEsc: string) =
        try 
            ignore <| decimalEscapeToByte decEsc
            true
        with 
        | :? System.OverflowException -> 
            false

    let normalizeDecimalEscape (decEsc: string) : string =
        sprintf "\\%03d" <| decimalEscapeToByte decEsc

    let private hexEscapeToByte (hexEsc: string) : byte =
        let hexdigits = hexEsc.Substring 2
        Byte.Parse (hexdigits, System.Globalization.NumberStyles.AllowHexSpecifier)

    // throws System.OverflowException if hex number is too big
    let private unicodeEscapeToUtf32 (unicodeEscape : string) : int =
        let hexdigits = unicodeEscape.Substring(3, unicodeEscape.Length - 4)
        Int32.Parse(hexdigits, System.Globalization.NumberStyles.AllowHexSpecifier)
        
    let isValidUnicodeEscape (unicodeEscape : string) =
        try 
            let codepoint = unicodeEscapeToUtf32 unicodeEscape
            0 <= codepoint && codepoint <= MaxUnicodeCodePoint
        with
        | :? System.OverflowException ->
            false

    // --- Unescaping to BlechString ---

    let decimalEscapeToString (decEsc : string) : BlechString = 
        [| decimalEscapeToByte decEsc |]

    let hexEscapeToString (hexEsc : string) : BlechString =
        [| hexEscapeToByte hexEsc |]

    


    // --- Unescaping to string, which is not a BlechString 

    let escapeToString (esc: string) : string = 
           Regex.Unescape esc // does the job for all defined Blech escapes sequences

    let unicodeEscapeToString (uniEsc : string) : string =
        unicodeEscapeToUtf32 uniEsc
        |> Char.ConvertFromUtf32


    /// This function replaces any end of line sequence by linefeed '\n'.
    let normalizeEndOfLine str =
        Regex.Replace(str, EndOfLine, Linefeed)

    
    /// This function removes line continuation in strings. 
    /// It assumes, that end of line is normalized to line feed
    let removeLineContinuations str = 
        Regex.Replace(str, LineContinuation, String.Empty)    
    

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
    

    let private isWhitespaceLine line = 
        Regex.IsMatch(line, WhitespaceOnly)
 
    let private isEmptyLine line = 
        String.Empty = line

    let private getTabCount line = 
        Regex.Match(line, TabIndentation).Length

    let private getIndentation line = 
        Regex.Match(line, Indentation).Value

    let findUnbalancedIndentations (lines: string list) =
        let mutable indent = None
        let unbalancedIndents =
            let mutable tabs = 0
            [ for i, line in List.indexed lines do  // The first line cannot contain tabs due to the lexer
                if i > 0 && not (isEmptyLine line) then // an empty line is always balanced
                    let lineIndent = getIndentation line
                    let tabCount = getTabCount line
                    if Option.isNone indent then
                        indent <- Some (i, lineIndent) // init indent
                        tabs <- tabCount               // the first tab indentation defines the standard 
                    else 
                        let _, tabsAndSpaces = Option.get indent
                        if tabCount = tabs then
                            if tabsAndSpaces.StartsWith lineIndent then
                                indent <- Some (i, lineIndent) // update indent
                        else // unbalanced tab count
                            yield i, lineIndent ]
        (indent, unbalancedIndents)

    // assumes balanced tab indentation
    let getCommonIndentation (lines: string list) = 
        let mutable commonIndent = None
        for i, line in List.indexed lines do
            if i > 0 then                               // the first line is not relevant
                if i = List.length lines - 1 ||         // the last line is always relevant
                   not (isWhitespaceLine line)  then    // whitespace lines are not relevant
                    let indent = getIndentation line
                    if Option.isNone commonIndent then  // first defining indentation
                        commonIndent <- Some indent
                    elif (Option.get commonIndent).StartsWith indent then
                        commonIndent <- Some indent
        
        Option.defaultValue "" commonIndent

    let indentationRange (mlsRange : Range.range) (line : int, indent : string) =
        let l = mlsRange.StartLine + line
        Range.range (mlsRange.FileIndex, l, 1, l, String.length indent)

    let splitMultiLineString (mlstr: string) =
        List.ofArray <| mlstr.Split Linefeed

    
    let private dedentLine (line : string) n = 
        try
            line.Substring n
        with
        | :? System.ArgumentOutOfRangeException -> 
            String.Empty

    let private dedentLines (lines: string list) = 
        let n = String.length <| getCommonIndentation lines
        [ for i, line in List.indexed lines do
            if i = 0 then // first line 
                yield line
            else 
                yield dedentLine line n ]

    let private removeEmptyFirstLine (lines: string list) = 
        if lines.[0] = String.Empty then List.tail lines
        else lines


    let formatMultiLineString (lines: string list) =
        dedentLines lines
        |> removeEmptyFirstLine 
        |> String.concat Linefeed
        |> removeLineContinuations
