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

module SyntaxErrors =
    open Blech.Common
    open Blech.Common.Range
    
    type ParserError = 
        | InconsistentModuleName of moduleName: AST.StaticNamedPath
        | NotUnitOne of number: string * range: Range.range
        | UnexpectedEOF of range: Range.range * expectedTokens: string list * start: Range.range
        | UnexpectedEndOfInput of range: Range.range * start: Range.range
        | UnexpectedToken of token: string * range: Range.range * expectedTokens: string list * start: Range.range
        | UnexpectedSignatureMember of implementation: Range.range // * signatureHead: Range.range
        | UnexpectedModuleMember of prototype: Range.range // * moduleHead: Range.range
        | UnexpectedExposure of exposing: Range.range // * signatureHead: Range.range

        interface Diagnostics.IDiagnosable with
            member err.MainInformation =
                match err with
                | InconsistentModuleName moduleName ->
                    { range = moduleName.Range 
                      message = sprintf "module name '%s'is not consistent with the filesystem."
                                <| moduleName.dottedPathToString } 
                
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

                | UnexpectedSignatureMember implementation ->
                    { range = implementation
                      message = "unexpected implementation in interface file." }

                | UnexpectedModuleMember prototype ->
                    { range = prototype
                      message = "unexpected prototype in implementation file." }
    
                | UnexpectedExposure exposing ->
                    { range = exposing
                      message = "unexpected exposing in signature file." }

            member err.ContextInformation: Diagnostics.ContextInformation list= 
                match err with
                | InconsistentModuleName moduleName ->
                    [ { range = moduleName.Range 
                        message = "should map to file and/or directory."
                        isPrimary = true } ]
                
                | UnexpectedToken (_token, range, _, start) ->
                    [ { range = start; message = "start of chunk."; isPrimary = false }
                      { range = range; message = "unexpected token."; isPrimary = true } ]
                
                | _ ->
                    []

            member err.NoteInformation = 
                match err with
                | InconsistentModuleName _ ->
                    [ "check file name and source path." ]
                
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
                
                | UnexpectedModuleMember _ ->
                    [ "source is implementation file."
                      "prototype is not allowed." ]
                
                | UnexpectedSignatureMember _ ->
                    [ "source is interface file."
                      "implementation is not allowed." ]
                
                | UnexpectedExposure _ ->
                    [ "source is interface file."
                      "an interface file exposes everything." ]

                | _  ->
                    []


    type LexerError =
        | CommentNotClosed of here: Range.range * opened: Range.range
        | TabularUsed of here: Range.range
        | UnknownToken of token: string * here: Range.range
        | NotAPath of here: Range.range
        | EofInDocComment of here: Range.range
        
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
                      message = "incorrect path specification" }
                | EofInDocComment here ->
                    { range = here
                      message = "end of file in doc comment" }
                    
            member err.ContextInformation = 
                match err with
                | CommentNotClosed (opened = o) ->    
                    [ { range = o; message = "comment opened."; isPrimary = false } ]
                | TabularUsed here ->
                    [ { range = here; message = "tab character."; isPrimary = true } ]
                | UnknownToken (here = r) ->
                    [ { range = r; message = "wrong character."; isPrimary = true } ]
                | NotAPath (here = r) ->
                    [ { range = r 
                        message = "incorrect path specification" 
                        isPrimary = true } ]
                | EofInDocComment here ->
                    [ { range = here
                        message = "end of doc comment" 
                        isPrimary = true } ]
    

            member err.NoteInformation = 
                match err with
                |TabularUsed _ ->
                    [ "Insert spaces, tabs are not allowed in Blech source code." ]
                | UnknownToken _ ->
                    [ "Non-ASCII characters are not allowed in Blech source code."]
                | NotAPath _ ->
                    [ "An import path should be braced in angles: 'import <path>'." ]
                | CommentNotClosed _ ->
                    [ "Missing '*/'." ]
                | EofInDocComment _ ->
                    [ "A doc comment should be placed before a declaration."]


module ParserUtils = 
    open System.Numerics
    open System

    open Blech.Common
    open SyntaxErrors

    type ParserErrorInfo = 
        {
            lexeme: string option
            range: Range.range
            expectedTokens: string list
        }
    
    //type PackageHead = 
    //    { 
    //        currentModuleName: string
    //        isSignature: bool 
    //        range: Range.range 
    //    }
    //    static member Default = 
    //        { currentModuleName = ""; isSignature = false; range = Range.rangeStartup }
        
        
    type ParserContext = 
        {
            mutable currentModuleName: LongIdentifier
            mutable currentLoadWhat: Package.LoadWhat
            //mutable packageHead: PackageHead
            mutable errorTokenAccepted: bool
            mutable errorInfo : ParserErrorInfo option
            mutable diagnosticsLogger: Diagnostics.Logger 
        }

        static member Default = {
                currentModuleName = []
                currentLoadWhat = Package.Implementation
                // packageHead = PackageHead.Default 
                errorTokenAccepted = false
                errorInfo = None
                diagnosticsLogger = Diagnostics.Logger.create()
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
                  // packageHead = { PackageHead.Default with currentModuleName = moduleName } 
                  errorTokenAccepted = false
                  errorInfo = None
                  diagnosticsLogger = diagnosticsLogger }
    

        let getDiagnosticsLogger () = parserContext.diagnosticsLogger, Diagnostics.Phase.Parsing

        let isErrorTokenAccepted () = parserContext.errorTokenAccepted
        let setErrorTokenAccepted bool = 
            // printfn "Error token accepted: %b" bool
            parserContext.errorTokenAccepted <- bool

        let getModuleName () = parserContext.currentModuleName
        let getLoadWhat () = parserContext.currentLoadWhat
        //let isSignature () = parserContext.packageHead.isSignature
        let isInterface () = parserContext.currentLoadWhat = Package.Interface
        let isImplementation () = parserContext.currentLoadWhat = Package.Implementation
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
    
    let parseOne (nat: string, r: Range.range) =
        match System.Int32.TryParse(nat) with
        | (true,value) when value = 1 -> 
            ()
        | _ ->
            Diagnostics.Logger.logError 
            <|| ParserContext.getDiagnosticsLogger ()
            <| NotUnitOne (nat, r)


    /// Checks the correct module in the package head
    let checkModuleName (name: AST.StaticNamedPath) =
        if not (name.identifiers = ParserContext.getModuleName ()) then
            Diagnostics.Logger.logError
            <|| ParserContext.getDiagnosticsLogger ()
            <| InconsistentModuleName name 
            

    /// Checks if the static member appears in an implementation or interface context
    // no longer needed, fjg 11.12.19
    //let checkSourceContext (staticMember: AST.Member) =
    //    if ParserContext.isInterface () then
    //        if not staticMember.isInterface then
    //            Diagnostics.Logger.logError
    //            <|| ParserContext.getDiagnosticsLogger ()
    //            <| UnexpectedSignatureMember staticMember.Range
                
    //    else
    //        if staticMember.isInterface then
    //            Diagnostics.Logger.logError
    //            <|| ParserContext.getDiagnosticsLogger ()
    //            <| UnexpectedModuleMember staticMember.Range 
                
    //    staticMember


    /// Checks the absence of exposing clauses in an interface context 
    let checkExposing (exposing: AST.Exposing option) =
        if ParserContext.isInterface () then
            if Option.isSome exposing then
                Diagnostics.Logger.logError
                <|| ParserContext.getDiagnosticsLogger ()
                <| UnexpectedExposure (Option.get exposing).Range       
    
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
            Diagnostics.Logger.logError
            <|| ParserContext.getDiagnosticsLogger ()
            <| parserError

    
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

module LexerUtils =

    open FSharp.Text.Lexing
    open Blech.Common

    open SyntaxErrors
    open System.Text

    /// Allows for collecting a doc string and its range
    type DocStringBuilder() =
        let mutable doc: StringBuilder = new StringBuilder()
        let mutable range: Range.range = Range.range0

        member this.Init startRange =
            doc <- new StringBuilder()
            range <- startRange
            this
        
        member this.Append (text: string, textRange) =
            doc <- doc.Append(text)
            range <- Range.unionRanges range textRange
            this

        member this.DocString = doc.ToString()

        member this.Range = range

        member this.ToDoc = 
            doc.ToString(), range

    /// this mutable number is used to track the nesting of /* .. */ comments in the SkipComment rule
    // TODO: encapsulate as LexerContext
    let mutable fromStart: Range.range = Range.range0
    let mutable commentStart: Range.range option = None
    let mutable commentDepth = 0

    let mutable docString = new DocStringBuilder()
   
    

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

    /// reports error: comment not terminated
    let commentNotClosed (lexbuf : LexBuffer<char>) =
        assert Option.isSome commentStart
        Diagnostics.Logger.logError 
        <|| ParserUtils.ParserContext.getDiagnosticsLogger ()
        <| CommentNotClosed (getRange lexbuf, Option.get commentStart)


    /// reports error: usage of TABULATOR
    let tabularUsed (lexbuf : LexBuffer<char>) =
        Diagnostics.Logger.logError 
        <|| ParserUtils.ParserContext.getDiagnosticsLogger ()
        <| TabularUsed (getRange lexbuf)


    /// reports error: usage of non-ASCII character
    let unknownToken (lexbuf : LexBuffer<char>) =
        Diagnostics.Logger.logError 
        <|| ParserUtils.ParserContext.getDiagnosticsLogger ()
        <| UnknownToken (getLexemeAndRange lexbuf)
        
    
    /// reports error: wrong path syntax
    let notAPath (lexbuf: LexBuffer<char>) =
        Diagnostics.Logger.logError 
        <|| ParserUtils.ParserContext.getDiagnosticsLogger ()
        <| NotAPath (getRange lexbuf)
    

    /// reports error: doc comment before EOF
    let eofInDocComment docRange =
        Diagnostics.Logger.logError 
        <|| ParserUtils.ParserContext.getDiagnosticsLogger ()
        <|  EofInDocComment docRange
    