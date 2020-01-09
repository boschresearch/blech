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

module Blech.Frontend.ParsePkg

open System
    
open Blech.Common

open SyntaxUtils
open SyntaxUtils.ParserUtils
open BlechParser

let tokenTagToString token = 
    match tokenTagToTokenId token with
    (* ---- module system ---- *)
    | TOKEN_BLECH -> "blech"
    (* ---- annotations ---- *)
    | TOKEN_AT -> "@"
    | TOKEN_ATAT -> "@@"
    (* ---- module system ---- *)
    | TOKEN_MODULE -> "module"
    | TOKEN_IMPORT -> "import"
    | TOKEN_EXPOSES -> "exposes"
    | TOKEN_SIGNATURE -> "signature"
    (* ---- name spaces ---- *)
    | TOKEN_EXTENSION -> "extension"
    (* --- paths -----*)
    | TOKEN_FROMPATH -> "from <path>"
    (* --- doc comments --- *)
    | TOKEN_LINEDOC -> "/// <line doc comment>"
    | TOKEN_BLOCKDOC -> "/** <block doc comment> */"
    (* ---- predefined types ---- *)
    | TOKEN_BOOL -> "bool"
    | TOKEN_BITS8 -> "bits8"
    | TOKEN_BITS16 -> "bits16"
    | TOKEN_BITS32 -> "bits32"
    | TOKEN_BITS64 -> "bits64"
    | TOKEN_UINT8 -> "uint8"
    | TOKEN_UINT16 -> "uint16"
    | TOKEN_UINT32 -> "uint32"
    | TOKEN_UINT64 -> "uint64"
    | TOKEN_INT8 -> "int8"
    | TOKEN_INT16 -> "int16"
    | TOKEN_INT32 -> "int32"
    | TOKEN_INT64 -> "int64"
    | TOKEN_FLOAT32 -> "float32"
    | TOKEN_FLOAT64 -> "float64"
    (* --- user-defined types --- *)
    | TOKEN_TYPE -> "type"
    | TOKEN_NEWTYPE -> "newtype"
    | TOKEN_ENUM -> "enum"
    | TOKEN_STRUCT -> "struct"
    | TOKEN_SIGNAL -> "signal"
    (* --------- units of measure --------- *)
    | TOKEN_UNIT -> "unit"
    (* --- clocks --- *)
    | TOKEN_CLOCK -> "clock"
    | TOKEN_COUNT -> "count"
    | TOKEN_UP -> "up"
    | TOKEN_DOWN -> "down"
    | TOKEN_OFF -> "off"
    | TOKEN_JOIN -> "join"
    | TOKEN_MEET -> "meet"
    | TOKEN_TICK -> "tick"
    | TOKEN_ON -> "on"
    (* --------- actions --------- *)
    | TOKEN_EMIT -> "emit"
    | TOKEN_PAST -> "past"
    | TOKEN_ASSIGN -> "="
    | TOKEN_ASSUME -> "assume"
    | TOKEN_ASSERT -> "assert"
    (* --------- types (classes), activties, functions --------- *)
    | TOKEN_ACTIVITY -> "activity"
    | TOKEN_FUNCTION -> "function"
    | TOKEN_VAR -> "var"
    | TOKEN_LET -> "let"
    | TOKEN_REF -> "ref"
    | TOKEN_SINGLETON -> "singleton"
    | TOKEN_PARAM -> "param"
    | TOKEN_CONST -> "const"
    | TOKEN_SHARES -> "shares"
    (* --------- FFI ---------------------- *)
    | TOKEN_EXTERN -> "extern" 
    (* --------- Blech statements --------- *)
    | TOKEN_ABORT -> "abort"
    | TOKEN_AWAIT -> "await"
    | TOKEN_COBEGIN -> "cobegin"
    | TOKEN_DEFAULT -> "default"
    | TOKEN_DO -> "do"
    | TOKEN_ELSE -> "else"
    | TOKEN_ELSEIF -> "elseif"
    | TOKEN_END -> "end"
    | TOKEN_FOR -> "for"
    | TOKEN_IF -> "if"
    | TOKEN_IN -> "in"
    | TOKEN_OF -> "of"
    | TOKEN_PRINT -> "print"
    | TOKEN_REPEAT -> "repeat"
    | TOKEN_RUN -> "run"
    | TOKEN_RESET -> "reset"
    | TOKEN_RETURN -> "return"
    | TOKEN_RETURNS -> "returns"
    | TOKEN_SUSPEND -> "suspend"
    | TOKEN_THEN -> "then"
    | TOKEN_TRY -> "try"
    | TOKEN_THROW -> "throw"
    | TOKEN_THROWS -> "throws"
    | TOKEN_ERROR -> "error"
    | TOKEN_UNTIL -> "until"
    | TOKEN_WEAK -> "weak"
    | TOKEN_WHEN -> "when"
    | TOKEN_WHILE -> "while"
    | TOKEN_WITH -> "with"
    (* --------- expressions and operators --------- *)
    | TOKEN_TRUE -> "true"
    | TOKEN_FALSE -> "false"
    (* logical operators *)
    | TOKEN_AND -> "and"
    | TOKEN_OR -> "or"
    | TOKEN_NOT -> "not"
    (* arithmetic saturation operators *)
    | TOKEN_ADD -> "+"
    | TOKEN_SUB -> "-"
    | TOKEN_MUL -> "*"
    | TOKEN_DIV -> "/"
    | TOKEN_MOD -> "%"
    | TOKEN_HAT -> "^"
    (* overflow operators *)
    | TOKEN_OADD -> "&+"
    | TOKEN_OSUB -> "&-"
    | TOKEN_OMUL -> "&*"
    (* bitwise operators *)
    | TOKEN_BAND -> "&"
    | TOKEN_BOR -> "|"
    | TOKEN_BXOR -> "~"
    | TOKEN_SHL -> "<<"
    | TOKEN_SHR -> ">>"
    (* comparison operators *)
    | TOKEN_EQU -> "=="
    | TOKEN_IEQ -> "!="
    | TOKEN_LES -> "<"
    | TOKEN_LEQ -> "<="
    | TOKEN_GRT -> ">"
    | TOKEN_GEQ -> ">="
    | TOKEN_AS -> "as"
    (* identity operators *)
    | TOKEN_IDEQU -> "=="
    | TOKEN_IDIEQ -> "!=="
    (* length operators on arrays and slices *)
    | TOKEN_LEN -> "len"
    | TOKEN_CAP -> "cap"
    (* -------------- Access operators ------------*)
    | TOKEN_PREV -> "prev"
    | TOKEN_NEXT -> "next"
    (* --------- delimiters and punctuations --------- *)
    | TOKEN_LBRACE -> "{"
    | TOKEN_RBRACE -> "}"
    | TOKEN_LBRACKET -> "["
    | TOKEN_RBRACKET -> "]"
    | TOKEN_LPAREN -> "("
    | TOKEN_RPAREN -> ")"
    | TOKEN_ELLIPSIS -> "..."
    | TOKEN_POINT -> "."
    | TOKEN_COLON  -> ":"
    | TOKEN_COMMA -> ","
    | TOKEN_SEMICOLON -> ";"
    | TOKEN_QUEST -> "?"
    (* | TOKEN_ELVIS -> "?:" *)
    (* --------- literals --------- *)
    | TOKEN_BINCONST -> "<binary number>"
    | TOKEN_OCTCONST -> "<octal number>"
    | TOKEN_HEXCONST -> "<hexadecimal number>"
    | TOKEN_NATCONST -> "<natural number>"
    | TOKEN_FLOATCONST
    | TOKEN_FLOATCONST32 -> "<floating point number>"
    | TOKEN_HEXFLOATCONST 
    | TOKEN_HEXFLOATCONST32 -> "<hexadicamal floating point number>"
    | TOKEN_STRING -> "<string constant>"
    | TOKEN_ID -> "<identifier>"
    | TOKEN_WILDCARD -> "<_>"
    | TOKEN_EOF -> "<EOF>"
    | TOKEN_EOL -> "<EOL>"
    | TOKEN_end_of_input-> "<EOF>"
    | TOKEN_error-> "<error>"

    
    
let private myBlechLexer lexbuf = 
    if ParserContext.isErrorTokenAccepted () then 
        BlechLexer.SkipLineOnError lexbuf
    else
        BlechLexer.Token lexbuf

 
let private myErrorHandler (lexbuf: FSharp.Text.Lexing.LexBuffer<char>) 
                            (ctxt: FSharp.Text.Parsing.ParseErrorContext<token>)  =

    let errInfo =
        let rng = LexerUtils.getRange lexbuf
        let expToks = 
                    ctxt.ReduceTokens @ ctxt.ShiftTokens
                    // |> List.filter (fun t -> not (tokenTagToTokenId t = TOKEN_error))    
                    |> List.map tokenTagToString 
        match ctxt.CurrentToken with
        | None ->
            { lexeme = None; range = rng; expectedTokens = expToks }
        | Some _  ->
            { lexeme = Some (LexerUtils.getLexeme lexbuf); range = rng; expectedTokens = expToks }

    ParserContext.storeParserErrorInfo errInfo

    
let private myBlechParser lexer lexbuf : AST.Package =
    let myTables = { BlechParser.tables() with parseError = myErrorHandler lexbuf }
    Operators.unbox <| myTables.Interpret(lexer, lexbuf, 0)
    // Todo: Catch exception from parser, in case error token cannot be accepted (which should not happen)


/// Parses a Blech module from a file given by its last argument.
/// The result is an untyped blech package, which could then be handed over to the
/// static analysis part.
let parseModule diagnosticLogger (loadWhat: Package.LoadWhat) (moduleName: SearchPath.ModuleName) (fileName: string) =
    Logging.log8 "ParsePkg.parseModule" 
    <| sprintf "%s: %s | file: %s | fileIndex: %d" (loadWhat.ToString()) 
                                                   (CommonTypes.idsToString moduleName) 
                                                   fileName 
                                                   (Range.fileIndexOfFile fileName)

    // Initialise global ParserContext
    ParserContext.initialise diagnosticLogger moduleName loadWhat
        
    // create a file index for current module's file in the global file index table
    ignore <| Range.fileIndexOfFile fileName

    // open stream from file
    let stream = new IO.StreamReader( IO.Path.GetFullPath(fileName) )
    
    // initialise lexing buffer
    let lexbuf = FSharp.Text.Lexing.LexBuffer<char>.FromTextReader stream
    lexbuf.EndPos <- { pos_bol = 0
                       pos_fname = fileName 
                       pos_cnum = 0
                       pos_lnum = 1 }
    
    // parse the file
    let utyPkg = myBlechParser myBlechLexer lexbuf

    // close the stream
    stream.Close()
    
    // handle errors
    let logger,_ = ParserContext.getDiagnosticsLogger()
    if Diagnostics.Logger.hasErrors logger then
        Error logger
    else
        Ok utyPkg

/// Parses a Blech module from a string given by its last argument.
/// The result is an either untyped blech package, 
/// or a Diagnostic
let parseModuleFromStrNoConsole diagnosticLogger fileName moduleName fileContents =
    // Initialise global ParserContext

    ParserContext.initialise diagnosticLogger moduleName Blech.Common.Package.Implementation 
    // TODO: change this, determine loadWhat from file extension for language server
        
    let stream = new IO.StringReader(fileContents)
    
    // intialise lexing buffer
    let lexbuf = FSharp.Text.Lexing.LexBuffer<char>.FromTextReader stream
    lexbuf.EndPos <- { pos_bol = 0
                       pos_fname = fileName // use module instead of file name 
                       pos_cnum = 0
                       pos_lnum = 1 }
    
    // parse the file
    let utyPkg = myBlechParser myBlechLexer lexbuf

    // close the stream
    stream.Close()
    
    // handle errors
    let logger,_ = ParserContext.getDiagnosticsLogger ()
    if Diagnostics.Logger.hasErrors logger then
        Error logger
    else
        Ok utyPkg
    
