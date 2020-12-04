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


namespace Blech.Frontend


module ExportInference = 

    open Blech.Common
    open Blech.Frontend.CommonTypes
    



    type Visibility =
        | Hidden
        | Exposed

    type private IsSimple = bool
    [<Literal>]
    let isSimple: IsSimple = true
    [<Literal>]
    let isNotSimple: IsSimple = false


    type Declared =
    | Import                     // all imported names, may become required imports
    | Type of isSimple: IsSimple // hidden type declarations, may become exported as opaque type
    | Singleton                  // hidden declared singletons, may become exported as opaque singleton


    type Defined =
    | RequiredImport
    | OpaqueType of isSimple: IsSimple
    | Type 
    | OpaqueSingleton
    | Singleton
    | Constant
    | Subprogram of calledSingletons: Name list


    type ExportContext = 
        {
            lookupTable : SymbolTable.LookupTable
            logger : Diagnostics.Logger
            exposed : Set<Name>     // The declaration name, that is exposed
            declarations : Map<Name, Declared> 
            definitions : Map<Name, Defined>
        }

        static member initialise (logger: Diagnostics.Logger) (lut: SymbolTable.LookupTable) = 
            { 
                lookupTable = lut
                logger = logger
                exposed = Set.empty
                declarations = Map.empty
                definitions = Map.empty
            }

    let private addDeclaration decl ctx name = 
        { ctx with declarations = ctx.declarations.Add (name, decl) }

    let private addDefinition def ctx name = 
        { ctx with definitions = ctx.definitions.Add (name, def) }

    let private addExposed ctx name =
        let declName = ctx.lookupTable.getDeclName name
        { ctx with exposed = ctx.exposed.Add declName}

    let private logExportError ctx err  = 
        do Diagnostics.Logger.logError ctx.logger Diagnostics.Phase.Exports err
        ctx
    
    let private show ctx =
        for n in ctx.exposed do
            printfn "Exposed: %A" n
        for n in ctx.declarations do
            printfn "Declared: %A Value: %A" n.Key n.Value
        for n in ctx.definitions do
            printfn "Defined: %A Value: %A" n.Key n.Value
            

    type ExportError = 
        | Dummy of range: Range.range * msg: string   // just for development purposes
    
        interface Diagnostics.IDiagnosable with
            member err.MainInformation =
                match err with
                | Dummy (rng, msg) ->
                    { range = rng
                      message = sprintf "Dummy error: %s" msg }
    
            member err.ContextInformation  = 
                match err with
                | Dummy (range = rng) ->
                    [ { range = rng; message = "thats wrong"; isPrimary = true } ]
    
            member err.NoteInformation = []


    // Members


    
    // ModuleSpec 
    let private inferExportExposing ctx (exposing: AST.Exposing) = 
        match exposing with
        | AST.Few (names, _) ->
            List.fold addExposed ctx names
        | AST.All _ ->
            failwith "Remove wildcard 'module exposes ...' completely"

    let private inferModuleSpec ctx (modSpec: AST.ModuleSpec) = 
        Option.fold inferExportExposing ctx modSpec.exposing


    // Imports
    let private inferImportExposing ctx (exposing: AST.Exposing) = 
        match exposing with
        | AST.Few (names, _) ->
            List.fold (addDeclaration Import) ctx names
        | AST.All _ -> // TODO: add all exposed names from imported modules
            failwith "Remove wildcard '...' completely"
            
    let private inferImport ctx (import: AST.Import) = 
        addDeclaration Import ctx import.localName
        |> Option.fold inferImportExposing <| import.exposing


    // Compilation Unit
    let private inferCompilationUnit (ctx: ExportContext) (cu: AST.CompilationUnit) =
        if cu.IsModule  then 
            List.fold inferImport ctx cu.imports
            |> Option.fold inferModuleSpec <| cu.spec
        else
            // ctx
            logExportError ctx <| Dummy (cu.Range, "Test error for non-module")


    let inferExports logger lookupTable (cu: AST.CompilationUnit) = 
        let ctx = ExportContext.initialise logger lookupTable
        let exports = inferCompilationUnit ctx cu
        // just for debugging
        show exports
        if Diagnostics.Logger.hasErrors exports.logger then
            Error exports.logger
        else
            Ok exports.definitions