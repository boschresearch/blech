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



module Blech.Compiler.ImportChecking

open System.Collections.Generic

open Blech
open Blech.Common
open Blech.Frontend

type TranslationUnitPath = TranslationUnitPath.TranslationUnitPath
type Logger = Diagnostics.Logger



type ModuleInfo = 
    {
        dependsOn: TranslationUnitPath list
        nameCheck: SymbolTable.Environment
        typeCheck: TypeCheckContext
        typedModule: BlechTypes.BlechModule
        translation: Backend.TranslationContext   // TODO: if this is not necessary, the whole Module can be moved to Frontend, fjg. 21.10.20
    }

    static member Make imports symbolTable typecheckContext blechModule translationContext =
        { 
            dependsOn = imports
            nameCheck = symbolTable
            typeCheck = typecheckContext
            typedModule = blechModule
            translation = translationContext
        }

type Imports = 
    private {
        imports: ResizeArray<TranslationUnitPath>
        compiled: Dictionary<TranslationUnitPath, Result<CompilationUnit.Module<ModuleInfo>, Logger>>
        logger: Logger
    }

    
    static member Initialise logger = 
        { imports = ResizeArray()
          compiled = Dictionary() 
          logger = logger }
    
    static member Empty = 
        Imports.Initialise <| Diagnostics.Logger.create()

    member this.GetImportedModules : TranslationUnitPath list = 
        Seq.toList ( this.imports )
       
    member this.AddImport moduleName result =
        if this.compiled.TryAdd(moduleName, result) then // The same module might be added more than once
            do this.imports.Add moduleName
        this
    
    member this.GetOkImports : ModuleInfo list = 
        [ for mn in this.imports do 
            let res = this.compiled.[mn]
            if Result.isOk res then yield (Result.getOk res).info ]

    member this.GetErrorImports : Logger list =
        [ for mn in this.imports do 
            let res = this.compiled.[mn]
            if Result.isError res then yield Result.getError res ]

    member this.GetTypeCheckContexts =
        this.GetOkImports
        |> List.map (fun i -> i.typeCheck)

    member this.GetTypedModules = 
        this.GetOkImports
        |> List.map (fun i -> i.typedModule)

    member this.GetTranslationContexts = 
        this.GetOkImports
        |> List.map (fun i -> i.translation)



let private checkImport (pkgCtx: CompilationUnit.Context<ModuleInfo>) (imports: Imports) (import: AST.Member) 
                : Imports = 
    match import with
    | AST.Member.Import i ->
        let loggerForImport = Diagnostics.Logger.create() // new module needs a fresh logger
        let moduleName = i.modulePath.path
        printfn "Create a new logger to require import: %s" <| string moduleName
        let res = CompilationUnit.require pkgCtx loggerForImport moduleName
        imports.AddImport moduleName <| res
    | AST.Member.Pragma _ ->
        imports
    | _ ->
        failwith "This should never happen"

let checkImports (pktCtx: CompilationUnit.Context<ModuleInfo>) logger (compUnit: AST.CompilationUnit) 
        : Imports = 
    let importCtx = Imports.Initialise logger
    List.fold (checkImport pktCtx) importCtx compUnit.imports