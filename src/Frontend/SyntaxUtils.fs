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

module Blech.Frontend.SyntaxUtils

open Constants
open CommonTypes

open System.Text.RegularExpressions


module SyntaxErrors =
    open Blech.Common
    open Blech.Common.Range
    
    type ParserError = 
        | ImportPathMalformed of string * Range.range
        | NotUnitOne of number: string * range: Range.range
        | UnexpectedEOF of range: Range.range * expectedTokens: string list * start: Range.range
        | UnexpectedEndOfInput of range: Range.range * start: Range.range
        | UnexpectedToken of token: string * range: Range.range * expectedTokens: string list * start: Range.range
                
        interface Diagnostics.IDiagnosable with
            member err.MainInformation =
                match err with        
                | ImportPathMalformed (msg, pos) ->
                    { range = pos
                      message = "malformed import path." }

                | NotUnitOne (number, range) ->
                    { range = range
                      message = sprintf "incorrent constant '%s' in unit expression, must be '1'." number }
                
                | UnexpectedEOF (range, _, _) ->
                    { range = range
                      message = "unexpected end of file." }
                
                | UnexpectedEndOfInput (range, _) ->
                    { range = range
                      message = "unexpected end of input." }
                
                | UnexpectedToken (token, range, _, _) ->
                    { range = range
                      message = sprintf "syntax error '%s'." token }

                
            member err.ContextInformation: Diagnostics.ContextInformation list= 
                match err with
                | UnexpectedToken (_token, range, _, start) ->
                    [ { range = start; message = "start of chunk."; isPrimary = false }
                      { range = range; message = "unexpected token."; isPrimary = true } ]
                
                | ImportPathMalformed (msg, pos) ->
                    [ { range = pos
                        message = msg 
                        isPrimary = true} ]
                
                | _ ->
                    []

            member err.NoteInformation = 
                match err with
                | UnexpectedEOF (_, expectedTokens, _) ->
                    List.fold 
                    <| fun acc -> fun tok -> sprintf "expected '%s'," tok :: acc
                    <| [ "or other token." ] 
                    <| expectedTokens
                
                | UnexpectedToken (_, _, expectedTokens, _) ->
                    List.fold 
                    <| fun acc -> fun tok -> sprintf "expected '%s'," tok :: acc
                    <| [ "or other token." ] 
                    <| expectedTokens
                
                | _  ->
                    []


    type LexerError =
        | CommentNotClosed of here: Range.range * opened: Range.range
        | TabularUsed of here: Range.range
        | UnknownToken of token: string * here: Range.range
        | NotAPath of here: Range.range
        | EofInDocComment of linedoc: Range.range
        | EofInString of string: Range.range
        | DecimalEscapeTooLarge of esc: string * rng: Range.range
        | UnicodeEscapeTooLarge of esc: string * rng: Range.range
        | EolInSingleLineString of rng: Range.range
        | InvalidLineTerminator of lt: string * rng: Range.range
        | UnbalancedIndentation of indent: Range.range * unbalanced: Range.range
        | BackslashWithoutEscape of here: Range.range
        | EscapeCurrentlyNotSupported of esc: string * rng: Range.range

        interface Diagnostics.IDiagnosable with
            member err.MainInformation =
                match err with
                | CommentNotClosed (here = r) ->
                    { range = r
                      message = "comment '/*' not terminated." } 
                | TabularUsed where ->
                    { range = where
                      message = "illegal character tab ('\\t') found." }
                | UnknownToken (token, here) ->
                    { range = here
                      message = sprintf "unexpected or illegal character '%s' found." token }
                | NotAPath (here = r) ->
                    { range = r
                      message = "incorrect path specification." }
                | EofInDocComment rng ->
                    { range = rng 
                      message = "end of file in doc comment." }
                | EofInString rng->
                    { range = rng
                      message = sprintf "end of file in string."}
                | DecimalEscapeTooLarge (esc, rng) ->
                    { range = rng
                      message = sprintf "decimal escape '%s' too large." esc }    
                | UnicodeEscapeTooLarge (esc, rng) ->
                    { range = rng
                      message = sprintf "unicode escape '%s' too large." esc }    
                | EolInSingleLineString rng ->
                    { range = rng
                      message = "end of line in single-line string."}
                | InvalidLineTerminator (lt, rng) ->
                    { range = rng
                      message = sprintf "invalid line terminator '%s'." lt } 
                | UnbalancedIndentation (indent, unbalanced) ->
                    { range = unbalanced 
                      message = "unbalanced indentation in multi-line string."}
                | BackslashWithoutEscape rng ->
                    { range = rng
                      message = "backslash '\\' does not start a valid escape sequence." }
                | EscapeCurrentlyNotSupported (esc, rng) ->
                    { range = rng
                      message = sprintf "Escape sequence '%s' is currently not supported." esc }

            member err.ContextInformation = 
                match err with
                | CommentNotClosed (opened = o) ->    
                    [ { range = o; message = "comment opened."; isPrimary = false } ]
                | TabularUsed here ->
                    [ { range = here; message = "tab character."; isPrimary = true } ]
                | UnknownToken (here = r) ->
                    [ { range = r; message = "wrong character."; isPrimary = true } ]
                | NotAPath (here = r) ->
                    [ { range = r; message = "incorrect path specification"; isPrimary = true } ]
                | EofInDocComment rng ->
                    [ { range = rng; message = "doc commment"; isPrimary = true}]    
                | EofInString rng->
                    [ { range = rng; message = "string"; isPrimary = true } ]
                | DecimalEscapeTooLarge (_, rng)
                | UnicodeEscapeTooLarge (_, rng) ->
                    [ { range = rng; message = "too large"; isPrimary = true} ]
                | EolInSingleLineString rng ->
                    [ { range = rng; message = "eol"; isPrimary = true } ]   
                | InvalidLineTerminator (_, rng) ->
                    [ { range = rng; message = "line terminator"; isPrimary = true } ]   
                | UnbalancedIndentation (indent, unbalanced) ->
                    [ { range = indent; message = "given indent"; isPrimary = false }
                      { range = unbalanced; message = "unbalanced indent"; isPrimary = true } ] 
                | BackslashWithoutEscape rng ->
                    [ { range = rng; message = "no escape"; isPrimary = true } ]   
                | _ -> 
                    []
    
            member err.NoteInformation = 
                match err with
                | TabularUsed _ ->
                    [ "Tabs are only allowed for indentation. Otherwise:"
                      "Use spaces in source code."
                      "Use '\\t' in character and string literals." ]
                | UnknownToken _ ->
                    [ "Non-ASCII characters are not allowed in Blech source code." ]
                | NotAPath _ ->
                    [ "An import path should be braced in angles: 'import <path>'." ]
                | CommentNotClosed _ ->
                    [ "Missing '*/'." ]
                | EofInDocComment _ ->
                    [ "A doc-comment must not appear at the end of a file." 
                      "Close a block doc-comment with '*/'." ]
                | EofInString _ ->
                    [ "The string is not closed." 
                      "Close a single-line string with '\"'." 
                      "Close a multi-line string with '\"\"\"'." ]
                | DecimalEscapeTooLarge _ ->
                    [ "A decimal escape sequence '\ddd' specifies a byte in a literal string:"
                      "'ddd' specifies the numeric value with up to three decimal digits."
                      "Note that if a decimal escape sequence is to be followed by a digit,"
                      "it must be expressed using exactly three digits." ]
                | UnicodeEscapeTooLarge _ ->
                    [ "A unicode escape sequence '\u{XXX}' specifies a unicode character."
                      "'XXX' specifies the code point with hexadecimal digits."
                      "'\u{0}' is the smallest code point."
                      "'\u{10FFFF}' is the largest code point." ]
                | EolInSingleLineString _ ->
                    [ "A single-line string must not contain an end of line."
                      "Use a line continuation '\<eol>' or a multi-line string." ]
                | InvalidLineTerminator _ ->
                    [ "Unicode line terminators are not a allowed in Blech source code."
                      "Line Separator (LS), Paragraph Separator (PS) or Next Line (NEL) must be removed."]
                | UnbalancedIndentation _ ->
                    [ "All lines in a multi-line string must start with the same amount of tab '\\t' indentation." 
                      "Tabs can only be used for indentation at the start of a new line." ]
                | BackslashWithoutEscape _ ->
                    [ "A backslash '\\' always starts an escape sequence."
                      "To introduce a single '\\' character use '\\\\'."
                      "Valid escapes are: '\\a', '\\b', '\\f', '\\n', '\\r', '\\t', '\\v', '\\'', '\\\"'."
                      "Use '\\ddd' with up to 3 decimal digits for decimal escapes."
                      "Use '\\xXX' with exactly 2 hexadecimal digits for hex escapes."
                      "Use '\\u{XXX}' with at least 1 hexadecimal digit for unicode escapes."]
                | _ -> 
                    []
    

module ParserUtils = 
    
    open System
    open System.Numerics

    open Blech.Common
    open Blech.Common.TranslationUnitPath

    open SyntaxErrors


    type ParserErrorInfo = 
        {
            lexeme: string option
            range: Range.range
            expectedTokens: string list
        }
    
    
    type ParserContext = 
        {
            mutable currentModuleName: TranslationUnitPath
            mutable currentLoadWhat: CompilationUnit.ImplOrIface
            mutable errorTokenAccepted: bool
            mutable errorInfo : ParserErrorInfo option
            mutable diagnosticsLogger: Diagnostics.Logger 
            mutable auxWildcardIndex : int  // unique for every compiled file
            mutable nameIndex : int // unique for every recursive compilation
        }

        static member Default = {
                currentModuleName = TranslationUnitPath.Empty
                currentLoadWhat = CompilationUnit.Blc
                errorTokenAccepted = false
                errorInfo = None
                diagnosticsLogger = Diagnostics.Logger.create()
                auxWildcardIndex = 0
                nameIndex = 0
            }
    
            
    [<RequireQualifiedAccess>]
    [<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
    /// This is singleton, which currently prevents parallel parsing
    module ParserContext =
        let mutable private parserContext = ParserContext.Default
        
        let initialise diagnosticsLogger moduleName loadWhat = 
            parserContext <- 
                { currentModuleName = moduleName
                  currentLoadWhat = loadWhat
                  errorTokenAccepted = false
                  errorInfo = None
                  diagnosticsLogger = diagnosticsLogger 
                  auxWildcardIndex = 0  // reinitialised for every compiled file
                  nameIndex = parserContext.nameIndex}  // incremented for every name accross all file during recursive compilation
    

        let getDiagnosticsLogger () = parserContext.diagnosticsLogger, Diagnostics.Phase.Parsing

        let isErrorTokenAccepted () = parserContext.errorTokenAccepted
        let setErrorTokenAccepted bool = 
            // printfn "Error token accepted: %b" bool
            parserContext.errorTokenAccepted <- bool

        let getModuleName () = parserContext.currentModuleName
        // let getLoadWhat () = parserContext.currentLoadWhat
        //let isSignature () = parserContext.packageHead.isSignature
        let isInterface () = parserContext.currentLoadWhat = CompilationUnit.Blh
        let isImplementation () = parserContext.currentLoadWhat = CompilationUnit.Blc
        //let getHeadRange () = parserContext.packageHead.range
        //let setPackageHead isSignature range = 
        //    parserContext.packageHead <- { parserContext.packageHead with isSignature = isSignature; range = range }


        /// Stores a parser's error info, for later logging. Asserts there is no other unlogged parser error
        let storeParserErrorInfo err  = 
            assert Option.isNone parserContext.errorInfo  
            parserContext.errorInfo <- Some err
        
        
        /// Consumes the last parser error info
        let consumeParserErrorInfo () = 
            let lpe = parserContext.errorInfo
            parserContext.errorInfo <- None
            lpe
        
        /// This never clashes with a Blech identifier
        /// Starts with '<wildcard>0' for every parsed file during a recursive compilation
        //let mkAuxIdentifierFromWildCard wildcard =
        //    let cur = parserContext.auxWildcardIndex
        //    parserContext.auxWildcardIndex <- cur + 1
        //    // printfn "Aux index: %d" cur
        //    sprintf "%s%s" wildcard (string cur) 

        
        let private newNameIndex () = 
            parserContext.nameIndex <- parserContext.nameIndex + 1
            parserContext.nameIndex

        /// Creates a name with a unique index across all files during a recursive compilation
        let mkName (id : Identifier) (range : Range.range) : Name = 
            { id = id 
              range = range 
              index = newNameIndex () }

        let mkEmptyName = 
            { id = "" 
              range = Range.range0 
              index = -1 }

        let private newWildcardIndex () = 
            parserContext.auxWildcardIndex <- parserContext.auxWildcardIndex + 1
            parserContext.auxWildcardIndex
            

        /// This never clashes with a Blech name
        /// Starts with '<wildcard>1' for every parsed file during a recursive compilation
        let mkNameFromWildcard (wildcard : Identifier) (range: Range.range) : Name =
            let wcidx = newWildcardIndex()
            { id = sprintf "%s%s" wildcard <| string wcidx 
              range = range 
              index = newNameIndex () }  

        


        
    /// strips '_' from number, e.g. 100_000 -> 100000
    let private strip_ s =
        String.collect (fun c -> if c = '_' then "" else string c) s

    let parseBin (s:string): Bits =
        let bits = String.explode (strip_ s).[2..]
        let pows, _ = List.mapFoldBack (fun b i -> (if b = '1' then i else 0I),  i*2I) bits 1I
        let value = List.sum pows
        BAny (value, s)
        
    let parseOct (s:string): Bits =
        let octs = String.explode (strip_ s).[2..]
        // 48 is the ascii offset for digits
        let pows, _ = List.mapFoldBack (fun b i ->  bigint (int b - 48) * i,  i*8I) octs 1I
        let value = List.sum pows
        BAny (value, s)
        

    let parseHex (s:string): Bits =
        // add a leading '0' to prevent interpretation as negative number
        let value = BigInteger.Parse("0" + (strip_ s).[2..], System.Globalization.NumberStyles.AllowHexSpecifier)
        BAny (value, s)
        
    let parseInteger (s:string): Int =
        let value = BigInteger.Parse (strip_ s)
        IAny (value, Some s)

    let parseFloat (s:string) : Float =
        try
            let v = System.Double.Parse((strip_ s), System.Globalization.NumberFormatInfo.InvariantInfo)
            let r = Some s 
            FAny (v, r)
        with
            | :? System.OverflowException ->
                FAny ( System.Double.PositiveInfinity, Some s )

    //let parseFloat floatParser s = 
    //    try
    //        ignore <| floatParser((strip_ >> stripF) s, System.Globalization.NumberFormatInfo.InvariantInfo)
    //        Ok s
    //    with 
    //    | _ -> Error s

    // let parseFloat64 = parseFloat System.Double.Parse

    //let parseFloat32 =
    //    parseFloat System.Single.Parse
    //    >> Result.map (fun x -> x.Replace("f","").Replace("F",""))
    
    
    //let private parseHexFloat hexfloat =
    //    // Follows the algorithm from 
    //    // “What Every Computer Scientist Should Know About Floating-Point Arithmetic”
    //    // http://pages.cs.wisc.edu/~david/courses/cs552/S12/handouts/goldberg-floating-point.pdf
    //    // adopted  to a hexadecimal representation
    //    //    First read in all hexadecimal digits as a bigint N, ignoring the hexadecimal point. [..] 
    //    //    Next, find the appropriate power 2**p necessary to scale N. 
    //    //    This will be a combination of the exponent of the hexadecimal number, 
    //    //    together with the position of the (up until now) ignored hexadecimal point. 
    //    //    [..] Finally, multiply (or divide if p < 0) N and 2**P.

    //    let s = (strip_ hexfloat).[2..]   // Ox1.Fp2 -> 1.Fp2 , 0x8.AF -> 8.AF
        
    //    let significant, exponent =
    //        match s.Split [|'p'; 'P'|] with
    //        | [|m; e|] -> m    , e      // 1.Fp2 -> 1.F , 2
    //        | m        -> m.[0], "0"    // 8.AF  -> 8.AF, 0
            
    //    let digits, pos = 
    //        match significant.Split '.' with
    //        | [|m ; f |] -> m + f, f.Length  // 8AF. -> 8AF, 0 // 8.AF -> 8AF, 2 // .8AF -> 8AF, 3
    //        | m          -> m.[0], 0         // 8AF  -> 8AF, 0

    //    try 
    //        let p = Int32.Parse(exponent) - (4 * pos)
    //        // add a leading '0' to prevent interpretation as a negative number
    //        let n = BigInteger.Parse("0" + digits, System.Globalization.NumberStyles.AllowHexSpecifier)
    //        if p < 0 then
    //            double n / double (2I**(-p))
    //        else
    //            double n * double (2I**p)
    //        |> floatToString |> Ok
    //    with
    //        | :? System.OverflowException ->
    //            Error hexfloat

    //let parseHexFloat64 = parseHexFloat >> Result.bind parseFloat64
    //let parseHexFloat32 = parseHexFloat >> Result.bind parseFloat32
    
    let parseHexFloat (repr: string) : Float =
        // Follows the algorithm from 
        // “What Every Computer Scientist Should Know About Floating-Point Arithmetic”
        // http://pages.cs.wisc.edu/~david/courses/cs552/S12/handouts/goldberg-floating-point.pdf
        // adopted  to a hexadecimal representation
        //    First read in all hexadecimal digits as a bigint N, ignoring the hexadecimal point. [..] 
        //    Next, find the appropriate power 2**p necessary to scale N. 
        //    This will be a combination of the exponent of the hexadecimal number, 
        //    together with the position of the (up until now) ignored hexadecimal point. 
        //    [..] Finally, multiply (or divide if p < 0) N and 2**P.

        let s = (strip_ repr).[2..]   // Ox1.Fp2 -> 1.Fp2 , 0x8.AF -> 8.AF
        
        let significant, exponent =
            match s.Split [|'p'; 'P'|] with
            | [|m; e|] -> m    , e      // 1.Fp2 -> 1.F , 2
            | m        -> m.[0], "0"    // 8.AF  -> 8.AF, 0
            
        let digits, pos = 
            match significant.Split '.' with
            | [|m ; f |] -> m + f, f.Length  // 8AF. -> 8AF, 0 // 8.AF -> 8AF, 2 // .8AF -> 8AF, 3
            | m          -> m.[0], 0         // 8AF  -> 8AF, 0

        let value = 
            try 
                let p = Int32.Parse(exponent) - (4 * pos)
                // add a leading '0' to prevent interpretation as a negative number
                let n = BigInteger.Parse("0" + digits, System.Globalization.NumberStyles.AllowHexSpecifier)
                if p < 0 then
                    double n / double (2I**(-p))
                else
                    double n * double (2I**p)
            with
                | :? System.OverflowException ->
                    Double.PositiveInfinity
        FAny (value, Some repr)
    
    
    // error reporting functions for parser
    let private reportError e = 
        Diagnostics.Logger.logError 
        <|| ParserContext.getDiagnosticsLogger ()
        <| e


    let parseOne (nat: string, r: Range.range) = // TODO: dead code? fg 26.01.21
        match System.Int32.TryParse(nat) with
        | (true,value) when value = 1 -> 
            ()
        | _ ->
            reportError <| NotUnitOne (nat, r)

    let parseImportPath pos strToParse =
        let currentPath = ParserContext.getModuleName ()
        match makeFromPath currentPath strToParse with
        | Ok tup -> 
            { AST.ModulePath.range = pos
              AST.ModulePath.path = tup }
        | Error (msg, colOffset) ->
            let errStart = Range.pos(pos.Start.Line, pos.Start.Column + colOffset)
            let errPos = Range.mkFileIndexRange pos.FileIndex errStart pos.End
            reportError <| ImportPathMalformed (msg, errPos)
            { range = pos
              path = TranslationUnitPath.Empty }

       
    /// Logs the last stored parser error
    let logParserError startRange =
        // printfn "logParserErrorCall"
        let pei = ParserContext.consumeParserErrorInfo ()
        match pei with
        | None -> // no parser error stored because of yacc's error recovery strategy
            ()
        | Some {lexeme = l; range = r; expectedTokens = ets} ->
            let parserError = 
                match l with
                | Some "" ->
                    UnexpectedEOF (range = r, expectedTokens = ets, start = startRange)
                | Some tok->
                    UnexpectedToken ( token = tok,
                                      range = r,
                                      expectedTokens = ets,
                                      start = startRange )
                | None ->
                    UnexpectedEndOfInput (range = r, start = startRange)
            reportError parserError

    
    let getStartOfLine (r: Range.range) =
        let startL = r.StartLine
        Range.range (r.FileIndex, startL, 1, startL, 1)


    let getStartOfFile (r: Range.range) =
        Range.range (r.FileIndex, 1, 1, 1, 1)


    let private docToAnnotation docAttrKey (text, range: Range.range) =
        let key = AST.Ident (docAttrKey, range.StartRange)
        let value = AST.Literal.String (text, range)        
        let keyValue = AST.Attribute.KeyValue (key, value, range)
        AST.Annotation(keyValue, range)

    let lineDocToAnnotation = docToAnnotation Attribute.Key.linedoc
    
    let blockDocToAnnotation = docToAnnotation Attribute.Key.blockdoc


    let makePreemption range preemption conditions body = 
        match preemption with
        | CommonTypes.Abort ->
            AST.Preempt (range, CommonTypes.Abort, conditions, CommonTypes.Before, body)
        | CommonTypes.Suspend ->
            AST.Preempt (range, CommonTypes.Suspend, conditions, CommonTypes.Before, body)
        | CommonTypes.Reset -> 
            let abortFinished = ParserContext.mkName (CommonTypes.mkPrefixIndexedNameFrom "abortFinished") range 
            AST.rewriteResetToAbortInLoop abortFinished range conditions body



module LexerUtils =

    open FSharp.Text.Lexing
    open Blech.Common

    open SyntaxErrors
    open System
    open System.Text

    /// Allows for collecting a doc strings, strings, and triple quoted strings and their range
    type TokenBuilder() =
        let mutable text: StringBuilder = StringBuilder()
        let mutable range: Range.range = Range.range0

        member this.Init startRange =
            text <- StringBuilder()
            range <- startRange
        
        member this.Append (str: string, rng: Range.range) =
            text <- text.Append(str)
            range <- Range.unionRanges range rng

        member this.Text = 
            text.ToString()

        member this.Range = 
            range

        member this.Token = 
            text.ToString(), range


    /// this mutable number is used to track the nesting of /* .. */ comments in the SkipComment rule
    // TODO: encapsulate as LexerContext
    let mutable commentStart: Range.range option = None
    let mutable commentDepth = 0

    let mutable tokenBuilder = TokenBuilder()
    

    let getLexeme (lexbuf: LexBuffer<char>) = 
        let l = System.String(lexbuf.Lexeme)
        // printfn "Lexeme: %s" l
        l


    let getRange (lexbuf: LexBuffer<char>): Range.range = 
        let f = lexbuf.StartPos.FileName
        let bl = lexbuf.StartPos.Line
        let bc = lexbuf.StartPos.Column + 1
        let el = lexbuf.EndPos.Line
        let ec = lexbuf.EndPos.Column
        Range.range (Range.fileIndexOfFile f, bl, bc, el, ec)
        

    let getLexemeAndRange lexbuf = 
        let l = getLexeme lexbuf
        let r = getRange lexbuf
        (l, r)


    // error reporting functions for lexer
    let private reportError e = 
        Diagnostics.Logger.logError 
        <|| ParserUtils.ParserContext.getDiagnosticsLogger ()
        <| e

    /// reports usage of unusual unicode line terminator
    let unicodeLineTerminator lexbuf =
        reportError <| InvalidLineTerminator (getLexemeAndRange lexbuf)
        
    /// reports error: usage of tab '\t'
    let tabularUsed (lexbuf : LexBuffer<char>) =
        reportError <| TabularUsed (getRange lexbuf)


    /// reports error: usage of non-ASCII character
    let unknownToken (lexbuf : LexBuffer<char>) =
        reportError <| UnknownToken (getLexemeAndRange lexbuf)
        
    
    /// reports error: wrong path syntax
    let notAPath (lexbuf: LexBuffer<char>) =
        reportError <| NotAPath (getRange lexbuf)
    

    let tabInCode lexbuf =
        let lxm, rng = getLexemeAndRange lexbuf
        // tabs '\t' are only allowed for line indentation
        if lexbuf.StartPos.Column > 0 then 
            reportError <| TabularUsed rng

    // --- end of file (eof) handling


    let eofInBlockComment lexbuf = 
        reportError <| CommentNotClosed (getRange lexbuf, Option.get commentStart)

    let eofInString lexbuf =
        reportError <| EofInString tokenBuilder.Range

    // doc comments 

    let eofInDocComment lexbuf =
        reportError <| EofInDocComment tokenBuilder.Range

    let unicodeLineTerminatorInDocComment lexbuf=
        let lr = getLexemeAndRange lexbuf
        reportError <| InvalidLineTerminator lr
        tokenBuilder.Append lr

    let validTokenInDocComment lexbuf =
        tokenBuilder.Append (getLexemeAndRange lexbuf)


    // let eofInCharacter lexbuf = eofInLexerContext "character"

    //--- Single-line and multi-line string parsing ---

    let startString lexbuf =
        tokenBuilder.Init (getRange lexbuf)
        
    let validTokenInString lexbuf =
        tokenBuilder.Append (getLexemeAndRange lexbuf)

    let lineContinuationInSingleLineString lexbuf =
        tokenBuilder.Append (String.Empty, getRange lexbuf)

    let lineContinuationInMultiLineString lexbuf =
        let lncont, rng = getLexemeAndRange lexbuf
        let normlncont = BlechString.normalizeEndOfLine lncont
        tokenBuilder.Append (normlncont, rng)

    let eolInSingleLineString lexbuf = 
        let lxm, rng = getLexemeAndRange lexbuf
        reportError <| EolInSingleLineString rng
        tokenBuilder.Append (lxm, rng)

    let eolInMultiLineString lexbuf =
        // replace eol by line feed '\n'
        tokenBuilder.Append (BlechString.Linefeed, getRange lexbuf)

    let tabInSingleLineString lexbuf =
        let lxm, rng = getLexemeAndRange lexbuf
        reportError <| TabularUsed rng
        tokenBuilder.Append (lxm, rng)

    let unicodeLineTerminatorInString lexbuf=
        let lr = getLexemeAndRange lexbuf
        reportError <| InvalidLineTerminator lr
        tokenBuilder.Append lr

    let tabInMultiLineString lexbuf =
        let lxm, rng = getLexemeAndRange lexbuf
        // tabs '\t' are only allowed for line indentation
        if lexbuf.StartPos.Column > 0 then 
            reportError <| TabularUsed rng
        tokenBuilder.Append (lxm, rng)
            
    let unicodeEscapeInString lexbuf =
        let esc, rng = getLexemeAndRange lexbuf
        let mutable unesc = esc
        if not <| BlechString.isValidUnicodeEscape esc then 
            reportError <| UnicodeEscapeTooLarge(esc, rng)
        else
            unesc <- BlechString.unicodeEscapeToString esc
        tokenBuilder.Append (unesc, rng)

    let decimalEscapeInString lexbuf =
        // TODO: make strings literals to byte arrays to support byte-size escapes
        let esc, rng = getLexemeAndRange lexbuf
        let mutable nesc = esc
        // let mutable unesc = esc
        if not <| BlechString.isValidDecimalEscape esc then 
            reportError <| DecimalEscapeTooLarge (esc, rng)
        else
        //    unesc <- BlechString.decimalEscapeToString esc
            reportError <| EscapeCurrentlyNotSupported (esc, rng)
        tokenBuilder.Append (nesc, rng)

    let hexEscapeInString lexbuf =
        // TODO: make strings literals to byte arrays to support byte-size escapes
        let esc, rng = getLexemeAndRange lexbuf
        // let unesc =  BlechString.hexEscapeToString esc
        reportError <| EscapeCurrentlyNotSupported (esc, rng)
        tokenBuilder.Append (esc, rng)

    let backslashInString lexbuf = 
        let bs, rng = getLexemeAndRange lexbuf
        reportError <| BackslashWithoutEscape rng
        tokenBuilder.Append (bs, rng)

    let escapeInString lexbuf =
        let esc, rng = getLexemeAndRange lexbuf
        let unesc = BlechString.escapeToString esc
        tokenBuilder.Append (unesc, rng)

    let private checkIndentations (lines: string list) rng = 
        let reportUnbalancedIndentations (indent, unbalancedIndents) =
            [ for ubi in unbalancedIndents do
                UnbalancedIndentation ( BlechString.indentationRange rng <| Option.get indent, 
                                        BlechString.indentationRange rng ubi ) ]
            |> List.map reportError 

        let unbalinds = BlechString.findUnbalancedIndentations lines
        if  List.isEmpty <| snd unbalinds then 
            true
        else 
            ignore <| reportUnbalancedIndentations unbalinds
            false

    let finishMultiLineString lexbuf = 
        let mls, rng = tokenBuilder.Token
        let lines = BlechString.splitMultiLineString mls
        if checkIndentations lines rng then
            BlechString.formatMultiLineString lines, rng
        else
            mls, rng

    let finishSingleLineString lexbuf =
        tokenBuilder.Append (String.Empty, getRange lexbuf) // Add range of closing " to token
        tokenBuilder.Token

    let unknownTokenInString lexbuf =
        unknownToken lexbuf  // TODO: separate error message
        tokenBuilder.Append (getLexemeAndRange lexbuf)


