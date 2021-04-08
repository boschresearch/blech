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

namespace Blech.Frontend

/// Uses nuget Package: https://github.com/polytypic/PPrint

module DocPrint =

    /// Constants and functions which are shared among different
    /// pretty printing modules (below).
    
    open System.Text.RegularExpressions
    open Blech.Common.PPrint
        
    let dpTabsize = 4

    let dpIndent = 
        indent dpTabsize
        
    /// Operator precedence mapping
    let dpPrec = 
        Map.ofList [ 
            ("min", 0); 
            (":", 5); ("as", 5);
            ("or", 10);
            ("and", 20);
            ("<", 30); ("<=", 30); (">", 30); (">=", 30); ("==", 30); ("!=", 30); ("===", 30); ("!==", 30)
            ("|", 40);
            ("^", 50); ("#", 50); ("##", 50); // TODO: stimmt das?
            ("&", 60);
            ("<<", 70); (">>", 70); ("+>>", 70); ("<>>", 70); ("<<>", 70); 
            ("+", 80); ("-", 80);
            ("*", 90); ("/", 90); ("%", 90);
            ("unary", 100); ("not", 100); ("~", 100);
            ("**", 110);
            ("max", 1000); ("parens", 1000) // TODO: stimmt das?
            ]      
        
        
    // Expression related functions
    let private precParens outerPrec docPrec doc =
        if outerPrec > docPrec then
            doc |> parens
        else 
            doc 

    let dpPrecedence outerPrec prec fdoc =
            (fdoc prec
            |> align)
            |> precParens outerPrec prec
            |> group

 
    // Functions for printing a list of things (comma separated with/without some brackets)
        
        
    let dpCommaSeparated docs = 
        docs
        |> punctuate comma
        |> vsep
        |> align
        |> group 

    let dpSeparated docs = 
        docs
        |> vsep
        |> align
        |> group 

    let private _dpCommaSeparatedInBrackets withBrackets docs =
        docs
        |> punctuate comma
        |> vsep
        |> align
        |> withBrackets
        |> group        

    let dpCommaSeparatedInParens = _dpCommaSeparatedInBrackets parens
    let dpCommaSeparatedInBraces : (Doc list -> Doc) = 
        _dpCommaSeparatedInBrackets braces
    let dpCommaSeparatedInBrackets : (Doc list -> Doc) = 
        _dpCommaSeparatedInBrackets brackets

    let dpToplevelClose docs =
        docs
        |> vsep
        //|> align
        //|> group

    let dpOptLinePrefix (optDoc: Doc option) doc =
        match optDoc with
        | Some od ->
            od <.> doc
        | None ->
            doc

    let dpOptSpacePrefix (optDoc: Doc option) doc =
        match optDoc with
        | Some prfx ->
            prfx <+> doc
        | None ->
            doc

    let dpOptSpacePostfix doc (optDoc: Doc option) =
        match optDoc with
        | Some pstfx ->
            doc <+> pstfx
        | None ->
            doc


    /// Convert a blech name to a Doc
    let dpName name = 
        txt <| name.ToString()

    /// Convert a blech auxiliary name
    /// see mkAuxIdentifierFromWildCard in file SyntaxUtils
    let dpModuleName modname = 
        let identifier = "_*[a-zA-Z]+[_a-zA-Z0-9]*"
        let wildcard = "_+"
        let m = Regex.Match(modname.ToString(), sprintf "%s|%s" identifier wildcard)
        txt m.Value

    let dpToplevel elements =
        elements
        |> punctuate line
        |> vsep

    let dpRemoveEmpty elements =
        elements
        |> Seq.filter (function
            | Empty -> false // remove empty documents from sequence
            | _ -> true)

    /// statement blocks (body of a control-flow structure)
    /// removes empty lines
    let dpBlock : Doc seq -> Doc =
        dpRemoveEmpty >> vsep

    // Printing of argument lists in particular
    let dpArguments = dpCommaSeparatedInParens


    let dpOptArguments prefix = function
        | [] -> 
            prefix
        | outputs -> 
            prefix <..> dpArguments outputs

    // Printing concurrentcy control flow blocks in particular
    let dpStrength = function
        | CommonTypes.Weak -> txt "weak"
        | CommonTypes.Strong -> empty
        
    let dpCobeginBlock (strength, block) =   
        txt "cobegin" <+> dpStrength strength <.>
        (dpBlock block
            |> indent dpTabsize)
        
    let dpWithBlock (strenght, block) =
        txt "with" <+> dpStrength strenght <.>
        (dpBlock block
            |> indent dpTabsize)
                  
    let dpCobegin = function
        | cobeginBlock :: withBlocks -> 
            (dpCobeginBlock cobeginBlock ::
                List.map (fun wb -> dpWithBlock wb) withBlocks
                |> vsep) <.>
            txt "end"
        | [] -> empty // never executed
    
    // Preemptions        
    let dpPreemption = function
        | CommonTypes.Abort ->
            txt "abort"
        | CommonTypes.Reset ->
            txt "reset"
        | CommonTypes.Suspend ->
            txt "suspend"

    let dpMoment = function 
        | CommonTypes.After ->
            txt "after"
        | CommonTypes.Before ->
            txt "before"
        | CommonTypes.OnNext -> 
            txt "next"

    let dpAliasedType = function
        | None -> empty
        | Some doc -> chr '=' <.> doc

    // Variable declaration related functions
    let dpTypeAnnotation = function 
        | None -> empty
        | Some doc -> chr ':' <+> doc

    let dpInitValue prefix = function
        | None -> prefix
        | Some doc -> prefix <+> chr '=' <.> doc

    
    let dpCall name arguments = 
        name <^> 
        (arguments |> dpArguments
            |> align
            |> group)


    // Printing of Blech subprogram calls
    let dpBlechCall name inputs optOutputs =
        name <^> 
        (inputs |> dpArguments
            |> dpOptArguments <| optOutputs
            |> align
            |> group)


    // Printing an annotation
    let dpAnnotation attribute =               // TODO: move this and functions from Signature printer to Blech printer, fjg 18.02.19
        chr '@' <^> brackets attribute


    // Printing a pragma - scope level annotation
    let dpPragma attribute =
        txt "@@" <^> brackets attribute


