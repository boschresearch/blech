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

[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Diagnostics =

    // Designed along 
    // https://microsoft.github.io/language-server-protocol/specification

    [<RequireQualifiedAccess>]
    type Level =
        | Bug
        | Fatal
        | PhaseFatal
        | Error
        | Warning
        | Note 
        | Help
        override l.ToString () = 
            match l with
            | Bug
            | Fatal
            | PhaseFatal
            | Error ->
                "error"
            | Warning ->
                "warn"
            | Note ->
                "info"
            | Help ->
                "hint"

    [<RequireQualifiedAccess>]
    type DiagnosticId = 
        | BlechC of int
        static member Create i = 
            BlechC i
        override code.ToString() =
            match code with
            | BlechC i -> System.String.Format ("{0:0000}", i)
        

    [<RequireQualifiedAccess>]
    type Phase = 
        | Default
        | Compiling
        | Parsing
        | Importing
        | Naming
        | Singletons
        | Exports
        | Typing
        | Causality
        | CodeGeneration
        override phs.ToString () = 
            match phs with
            | Default
            | Compiling -> "compiling"
            | Parsing -> "parsing"
            | Importing -> "importing"
            | Naming -> "name resolution"
            | Singletons -> "singleton inference"
            | Exports -> "export inference"
            | Typing -> "typing"
            | Causality -> "causality"
            | CodeGeneration -> "code generation"

    type Information = 
        {
            range: Range.range
            message: string
        }
        static member Create range message = 
            { range = range
              message = message }

    //[<RequireQualifiedAccess>]
    //type Origin = 
    //    | Main  
    //    | Sub

    type ContextInformation = 
        {
            range: Range.range
            message: string
            isPrimary: bool
        }
    //    static member Create range message origin = 
    //        { range = range; message = message; origin = origin}

    
    /// Type Diagnostic holds all information for diagnostic messages, i.e bugs, errors, warnings
    /// Diagnostics should be rendered in the style of Rust
  
    /// https://internals.rust-lang.org/t/new-error-format/3438
    /// https://github.com/rust-lang/rust/blob/2079a084df08c38eb4dbfc5c8de5c0245170c3d9/src/librustc_errors/diagnostic.rs
    /// https://github.com/brendanzab/codespan/blob/master/codespan-reporting/src/diagnostic.rs
    
    /// Rendered diagnostic message
    ///
    /// error: The access of the prev value of %s is forbidden on the left hand side (Error 42)
    ///     --> test.blc:107:1
    /// 107 |> prev x = 42
    ///     |> ^^^^ usage of prev occurs here
    ///
    /// form data
    /// diag = { 
    ///     level = Error
    ///     message = "The access of the prev value of %s is forbidden on the left hand side"
    ///     code = Some "42"
    ///     regios = [| {range = ...; label = Some "usage of prev occures here"; style = Primary} |]
    /// }


    /// The simplest Diagostic consists of a range and a message.

    type Diagnostic =
        {
            phase: Phase
            level: Level
            // code: DiagnosticId option  could be added and used for i18n (like in F#) 
            // and option --explain <diagnosticId> (like in Rust)
            main: Information
            context: ContextInformation list // can be empty
            note: string list // can be empty
        }
        member diag.isError =
            match diag.level with 
            | Level.Bug | Level.Fatal | Level.PhaseFatal | Level.Error -> true
            | _ -> false


    /// to be implemented by every error type
    type IDiagnosable =    
        abstract member MainInformation: Information
        abstract member ContextInformation: ContextInformation list
        abstract member NoteInformation: string list
        
    //[<RequireQualifiedAccess>]
    //[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
    //module Diagnostic =
    //    let create level information : Diagnostic =
    //        { level = level; main = information; context = []; help = []}
                
    //    let isError diagnostic : bool =
    //        match diagnostic.level with 
    //        | Level.Bug | Level.Fatal | Level.PhaseFatal | Level.Error -> true
    //        | _ -> false
        
    //    let addContext contextInfos diagnostic : Diagnostic = 
    //        { diagnostic with context = contextInfos }
            

    type Logger =
        private {
            mutable errorCount: int
            diagnostics: ResizeArray<Diagnostic>
        }   

    [<RequireQualifiedAccess>]
    [<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
    module Logger =

        let create () = 
            { errorCount = 0; diagnostics = ResizeArray() }
            
        let hasErrors logger =
            logger.errorCount > 0
        
        let addDiagnostic logger diagnostic =
            // make sure there are no multiple entried of the same error
            // may otherwise happen due to symmetric write-write errors and the like
            if not <| logger.diagnostics.Contains diagnostic then
                logger.diagnostics.Add diagnostic
                if diagnostic.isError then 
                    logger.errorCount <- logger.errorCount + 1

        // USAGE: let causalLogErr = log givenLogger Causality Error
        let private log logger phase level (err: IDiagnosable) =
            let diag = {
                phase = phase
                level = level
                main = err.MainInformation
                context = err.ContextInformation
                note = err.NoteInformation
            }
            addDiagnostic logger diag 

        let logFatalError logger phase err = 
            log logger phase Level.Fatal err 

        let logError logger phase err =
            log logger phase Level.Error err 
            
       
    
    [<RequireQualifiedAccess>]
    module Emitter =
        open System
        open Blech.Common

        let digitCount number = (int) (log10 ((float)number)) + 1
        let mutable fillWidth = 0   

        let private emitAsciiContext os prevLn (info: ContextInformation) =
            let loc = info.range
            let fstLn = loc.StartLine
            let lstLn = loc.EndLine
                
            if prevLn > fstLn then  // jump back in source
                Printf.bprintfn os "%s%s"
                <| String.fill fillWidth ' '
                <| "<<<"
            else if prevLn + 1 < fstLn then // skip lines in source 
                Printf.bprintfn os "%s%s"
                <| String.fill fillWidth ' ' 
                <| "..."
            
            let mutable fstCol = loc.StartColumn
            let mutable lstCol = loc.EndColumn

            for i in fstLn .. lstLn do
                let ln = (CodeMap.lineOfFile loc.FileName i).Replace('\t', ' ')  // Correct range counting by replacing '\t' with ' '
                let len = ln.Length

                Printf.bprintfn os "%d%s | %s" i 
                <| String.fill (fillWidth - digitCount i) ' ' 
                <| ln 
                                    
                if fstLn = lstLn then  
                    () // Nothing changes
                else if i = fstLn then
                    if len > lstCol then lstCol <- len
                else 
                    let lnFst = 
                        try 
                            let idx = List.findIndex 
                                      <| fun c -> not (' ' = c || Char.IsWhiteSpace c) 
                                      <| String.explode ln
                            idx + 1
                        with _ -> 
                            fstCol
                
                    if i < lstLn then
                        if len > lstCol then lstCol <- len
                        if lnFst < fstCol then fstCol <- lnFst
                    
                    else if i = lstLn then
                        if lnFst < fstCol then fstCol <- lnFst
                    
            if  lstCol >= fstCol then
                let len = lstCol - fstCol + 1 
                Printf.bprintfn os "%s | %s%s %s"
                <| String.fill fillWidth ' '
                <| String.fill (fstCol-1) ' '
                <| (String.fill len <| if info.isPrimary then '^' else '-') 
                <| info.message
            
            lstLn

        let private emitAsciiHelp (os: Text.StringBuilder) help =
            Printf.bprintfn os "%s%s" 
            <| String.fill fillWidth ' '
            <| help

        let private emitAsciiDiagnostic (os: Text.StringBuilder) (d: Diagnostic) =
            let lvl = string d.level
            let rng = d.main.range
            let msg = d.main.message
            let phs = d.phase
            
            if not (List.isEmpty d.context) then
                fillWidth <- digitCount (CodeMap.lineCountOfFile (List.head d.context).range.FileName)
            else 
                fillWidth <- 1

            Printf.bprintfn os "%s: %s" lvl msg
            
            Printf.bprintfn os "%s--> %s:%d:%d [%s]" 
            <| (String.fill fillWidth ' ') 
            <| rng.FileName 
            <| rng.StartLine 
            <| rng.StartColumn
            <| d.phase.ToString()
            
            if not (List.isEmpty d.context) then
                Printf.bprintfn os ""
                let fstLn = (List.head d.context).range.StartLine
                List.fold (emitAsciiContext os) fstLn d.context |> ignore
            
            if not (List.isEmpty d.note) then
                Printf.bprintfn os ""
                List.iter (emitAsciiHelp os) d.note
            
            Printf.bprintfn os ""
          
        let private emitLoggedDiagnostics (os: Text.StringBuilder) (dl: Logger) =
            Seq.iter (emitAsciiDiagnostic os) dl.diagnostics

        let printDiagnostics (dl: Logger) =
            let sb = Text.StringBuilder()
            emitLoggedDiagnostics sb dl
            //Console.OutputEncoding <- System.Text.Encoding.UTF8
            //Printf.fprintf Console.Out "%s" <| sb.ToString()
            Console.Out.Write(sb.ToString())

        let getDiagnostics (dl: Logger) =
            dl.diagnostics

    let wrapErrsInLogger logger phase errs =
        // let errLogger = Logger.create()
        let logError e = Logger.logError logger phase e
        do List.iter logError errs
        logger

    let printErrors logger phase errs =
        wrapErrsInLogger logger phase errs
        |> Emitter.printDiagnostics
            