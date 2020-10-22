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

module SymbolTable =

    open System.Collections.Generic
    
    open Blech.Common
    open Blech.Common.TranslationUnitPath
    
    open CommonTypes
    
    
    /// TODO @FJG: What is a symbol?
    type Symbol = 
        private {
            name: Name
            // access: AccessControl
            isScope: bool
        }
        static member Create name isScope =
            { name = name; isScope = isScope }
    
    
    /// TODO @FJG: What does it mean?
    [<RequireQualifiedAccess>]
    type Visibility = // a scope property
        | Open
        | Closed  // a closed scope cannot be accessed from outside


    [<RequireQualifiedAccess>]
    type Recursion =
        | Yes       // The scope id can be used recursively, e.g a structured type
        | No    // e.g a subprogram


    type Scope = 
        private {
            id: Identifier
            visibility: Visibility
            recursion: Recursion
            symbols: Map<Identifier, Symbol>
            innerscopes : Map<Identifier, Scope>    // added when scopes are left 
        }


    [<RequireQualifiedAccess>]
    [<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
    module Scope =
        
        let private globalId = "$Global"

        // this is a global state
        let private anonCounter = ref 0
        
        let init() =
            anonCounter := 0
            
        let nextAnonymousId () : Identifier =
            anonCounter := !anonCounter + 1
            string !anonCounter

        let addSymbol scope (symbol: Symbol)  =
            let id = symbol.name.id
            { scope with symbols = scope.symbols.Add (id, symbol)  }

        let containsSymbol scope (id : Identifier) : bool =
            scope.symbols.ContainsKey id
        
        let idIsNonRecursive scope (id: Identifier) =
            scope.id = id && scope.recursion = Recursion.No

        /// Tries to to find given symbol regardless of whether it is hidden or exposed
        let tryFindSymbol scope (id: Identifier) : Symbol option =
            scope.symbols.TryFind id
               
        /// Tries to find exposed symbols only
        //let tryFindPublicSymbol scope (id: Identifier) : Symbol option =
        //    scope.symbols.TryFind id
        //    |> Option.filter Symbol.isPublic
        
        /// Gets a symbol in the scope, raises KeyNotFoundException if it is not found
        let getSymbol scope (id: Identifier) : Symbol =
            scope.symbols.Item id

        let containsInnerScope scope id =
            scope.innerscopes.ContainsKey id
                        
        let addInnerScope scope innerscope : Scope =
            { scope with innerscopes = scope.innerscopes.Add (innerscope.id, innerscope) }

        let tryFindInnerScope scope id : Scope option=
            scope.innerscopes.TryFind id

        let allowsShadowing scope =
            scope.visibility = Visibility.Open

        let create id visibility recursion =
            { Scope.id = id
              visibility = visibility
              recursion = recursion
              symbols = Map.empty
              innerscopes = Map.empty }
    
        let createAnonymous () =
            let id = nextAnonymousId ()
            create id Visibility.Closed Recursion.No // always closed non-recursive, because id is generated

        let createGlobalScope () : Scope = // id : Scope = 
           create globalId Visibility.Open Recursion.No

        let rewriteId scope id : Scope =
            {scope with id = id}


    type NameInfo =
        | Decl of QName
        | Use of Name //TODO @FJG: please, clarify what Use is. When then name appears on the rhs? Is it not a "Use" when it is on the lhs?


    type LookupTable = 
        private { 
            lookupTable: Dictionary<Name, NameInfo>
        }

        static member Empty = { lookupTable = Dictionary() }

        //static member Join this that =
        //    let both = Seq.concat (seq{this.lookupTable; that.lookupTable})
        //    { lookupTable = Dictionary(both) }

        member this.AddLookupTable imported = 
            // lookuptables might be imported more than once via different local names
            // these duplicates must be ignored
            for pair in imported.lookupTable do
                ignore <| this.lookupTable.TryAdd (pair.Key, pair.Value)
            this

        override this.ToString () =
            [for pair in this.lookupTable -> pair.Key.id + " -> " + pair.Value.ToString()]
            |> String.concat "\n"

        member private lt.getQname name =
            let ok, info = lt.lookupTable.TryGetValue name
            if ok then 
                match info with
                | Decl qname -> Some qname
                | Use declName -> lt.getQname declName
             else 
                None

        // should be invisible outside this file
        member nqt.addDecl name qname =
            // printfn "addDecl: name: %A qname: %A" name qname
            nqt.lookupTable.Add (name, Decl qname)

        // should be invisible outside this file
        // assumes declare before use        
        member lt.addUsage usageName declName =
            // Artificially generated names use the same range multiple times
            // therefore it is possible that a key already exists
            ignore <| lt.lookupTable.TryAdd (usageName,  Use declName)

        member lt.Show = 
            let pairs = seq { for KeyValue(k,v) in lt.lookupTable do yield k, v }
            Seq.fold (fun s (k, v) -> s + string k + ": " + string v + "\n" ) "" pairs

        member this.nameToQname name = 
            match this.getQname name with
            | Some qname -> qname
            | None -> failwithf "failed to make QName for %A" name

        member private this.lastNameToQname path =
            List.last path |> this.nameToQname

        member this.spathToQname (path: AST.StaticNamedPath) =
            this.lastNameToQname path.path

        member private this.getNamePart (path: AST.DynamicAccessPath) =
            let pred name = match this.getQname name with Some _ -> true | None -> false
            path.leadingNames
            |> List.takeWhile pred

        member this.dpathToQname (path: AST.DynamicAccessPath) =
            this.getNamePart path |> this.lastNameToQname

        member this.decomposeDpath (path: AST.DynamicAccessPath) =
            let namePart = this.getNamePart path
            let subExprPart = path.path.[namePart.Length..] // empty, if namePart = path.path
            this.lastNameToQname namePart, subExprPart
            
            
    /// Context of the name resolution compiler phase
    /// The "path" is a stack which starts with an empty, global scope
    /// At the end, only the global scope remains but all subscopes will have been added as inner scopes
    /// Thus at the end, path is a singleton element list with a tree of scopes given by the innerscopes attributes
    type Environment = 
        {
            moduleName: TranslationUnitPath
            // imports: Dictionary<TranslationUnitPath, Environment>
            path: Scope list // sorted from current (innermost) to outermost
            lookupTable: LookupTable
        }
    
        
    type NameCheckError = 
        | ShadowingDeclaration of decl: Name * shadowed: Name                     // declaration name * shadowed name
        | NoDeclaration of usage: Name                                            // uname
        | NoDeclarationInDynamicAccess of usage:Name * access: AST.DynamicAccessPath         // usage  name * qualified access                     
        | NoDeclarationInStaticAccess of usage:Name * access: AST.StaticNamedPath
        | NoImplicitMemberDeclaration of access: AST.StaticNamedPath
        | NonUniqueImplicitMember of usage: AST.StaticNamedPath * decls: Name list list   // static path * declaration names
    
        interface Diagnostics.IDiagnosable with
            
            member err.MainInformation =
                match err with
                | ShadowingDeclaration (decl = d) ->
                    { range = d.Range 
                      message = sprintf "the declaration of '%s' shadows an existing declaration" d.id } 
                | NoDeclaration (usage = u) ->
                    { range = u.Range
                      message = sprintf "the identifier '%s' has no declaration" u.id }
                | NoDeclarationInDynamicAccess (usage, dpath) ->
                    { range = usage.Range
                      message = sprintf "the identifier '%s' has no declaration in qualified access '%s'" usage.idToString dpath.pathToString }
                | NoDeclarationInStaticAccess (usage, spath) ->
                    { range = usage.Range    
                      message = sprintf "the identifier '%s' has no declaration in qualified access '%s'" usage.idToString spath.dottedPathToString }
                | NoImplicitMemberDeclaration (spath) ->
                    { range = spath.Range
                      message = sprintf "the implicit member access '%s' has no declaration" spath.dottedPathToString }
                | NonUniqueImplicitMember (usage = spath) ->
                    { range = spath.Range
                      message = sprintf "the implicit member access '%s' is not unique" (spath.dottedPathToString) }

            member err.ContextInformation  = 
                match err with
                | ShadowingDeclaration (decl, shadowed) ->
                    [ { range = shadowed.Range; message = "existing declaration"; isPrimary = false }
                      { range = decl.Range; message = "shadowing declaration"; isPrimary = true } ] 
                | NoDeclaration (usage = u)
                | NoDeclarationInDynamicAccess (usage = u)
                | NoDeclarationInStaticAccess (usage = u) -> 
                    [ { range = u.Range; message = "no declaration found"; isPrimary = true } ]
                | NoImplicitMemberDeclaration (access = a) ->
                    [ { range = a.Range; message = "no suitable declaration found"; isPrimary = true } ]
                | NonUniqueImplicitMember (usage, decls) ->
                    //let decl = List.head decls
                    //let fst = List.head decl
                    //let lst = List.last decl
                    //let r = Range.mkRange fst.Range.FileName fst.Range.Start lst.Range.End
                    let declInfo names : Diagnostics.ContextInformation list=
                        List.map ( fun (name: Name)-> { range = name.Range ; message = ""; isPrimary = false } ) names
           
                    List.foldBack ( fun decl infos -> declInfo decl @ infos ) decls              
                        [ { range = usage.Range; message = "more than one declaration found"; isPrimary = true } ]
                    //|> List.append [ { range = r; message = "this is a test"; isPrimary = true } ]        

            member err.NoteInformation = []

    [<RequireQualifiedAccess>]        
    [<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
    module Environment =

        let init moduleName =
            do Scope.init ()   // initialize global state for anonymous scopes
            { Environment.moduleName = moduleName
              path = [ Scope.createGlobalScope () ]
              lookupTable = LookupTable.Empty }
        
        //let empty =
        //    { moduleName = TranslationUnitPath.Empty
        //      // imports = Dictionary()
        //      path = [Scope.createGlobalScope ()]
        //      lookupTable = LookupTable.Empty }
         
        let private currentScope (env: Environment) = 
            List.head env.path 

        let private parentScope env = 
            List.head (List.tail env.path)

        let private currentOuter env = 
            List.tail env.path

        let private parentOuter env = 
            List.tail (List.tail env.path)   // this is safe because of the global scope initialisation
        
        /// Starting from the innermost scope, try to find a scope that
        /// declares id and return Some if found, None otherwise.
        let private tryFindDeclarationScope env id =
            let rec tryFindDeclScope (path: Scope list) id =
                match path with
                | [] -> None
                | current :: _ when Scope.containsSymbol current id ->    // first in current scope
                    Some current
                // TODO @FJG: what situation does this case handle?
                | current :: _ :: outer when Scope.idIsNonRecursive current id -> // then prevent recursive use of id
                    // printfn "id: %s -> scope id: %s" id current.id
                    // None
                    tryFindDeclScope outer id
                | _ :: outer ->
                    tryFindDeclScope outer id

            tryFindDeclScope env.path id

        
        /// Returns a list of scopes names starting from the outermost scope in the current compilation unit
        let getQNamePrefix env : LongIdentifier = 
            List.rev env.path  
            |> List.tail  // dismiss the global scope
            |> List.map (fun scope -> scope.id)

        /// TODO @FJG: what is going on here?
        let private tryFindShadowedSymbol env id : Symbol option = 
            let rec shadows (path : Scope list) id =
                match path with
                | [] -> 
                    None
                | current :: _ when Scope.allowsShadowing current ->     // is shadwing allowed
                    None
                | current :: _ when Scope.containsSymbol current id ->   // is a shadowed symbol 'id' there
                    Scope.tryFindSymbol current id  // the shadowed symbol
                | current :: _ when Scope.idIsNonRecursive current id -> // can the scope name 'id' be shadowed
                    // printfn "id: %s -> scope id: %s" id current.id
                    None
                | _ :: outer ->
                    shadows outer id
            
            match Scope.tryFindSymbol (currentScope env) id with
            | Some s ->
                Some s
            | None ->
                shadows (currentOuter env) id

        let private insertSymbol env (name: Name) (label: IdLabel) isScope =
            match tryFindShadowedSymbol env name.id with
            | None ->
                let qname = QName.Create env.moduleName (getQNamePrefix env) name.id label
                try
                    do env.lookupTable.addDecl name qname
                with exp ->
                    printfn "%A" exp
                    // printf "%A" (env.lookupTable.ToString())
                let symbol = Symbol.Create name isScope
                let newEnv = { env with path = Scope.addSymbol (currentScope env) symbol :: currentOuter env }
                Ok newEnv
            | Some shadowed ->
                Error <| ShadowingDeclaration (name, shadowed.name)
         
        let insertName env (name: Name) (label: IdLabel) = 
            insertSymbol env name label false

        let insertScopeName env (name: Name) = 
            insertSymbol env name (IdLabel.Static) true

        //let addImport env (translationUnitPath, importedEnv) : Environment =
        //    do ignore <| env.imports.TryAdd(translationUnitPath, importedEnv)
        //    env

        //let init moduleName (envs: Environment list) =
        //    do Scope.init ()  // initialize global state for anonymous scopes
            
        //    // add imported files' scopes as innerscopes
        //    let importedScopes =
        //        let globalScope = Scope.createGlobalScope ()
        //        envs
        //        |> List.collect (fun env -> env.path)
        //        |> List.fold Scope.addInnerScope globalScope
        //    let importedLookupTables =
        //        envs
        //        |> List.map (fun env -> env.lookupTable)
        //        // |> List.fold LookupTable.Join LookupTable.Empty
        //        |> List.fold (fun (lt: LookupTable) ilt -> lt.AddLookupTable ilt) LookupTable.Empty
        //    let globalEnv =
        //        { Environment.moduleName = moduleName
        //          //imports = Dictionary()
        //          path = [importedScopes]
        //          lookupTable = importedLookupTables }
        //    // add imported files' scopes as symbols
        //    envs 
        //    |> List.collect (fun env -> env.path)
        //    |> List.fold (fun envRes scope -> 
        //        envRes
        //        |> Result.bind (fun env ->
        //            insertScopeName env {id = scope.id; range = Range.range0})) //TODO
        //        (Ok globalEnv)

        //let initEmptyTable moduleName = init moduleName []

        let private enterInnerScope env id visibility recursion =
            assert not (Scope.containsInnerScope (currentScope env) id)
            let scp = Scope.create id visibility recursion
            // printfn "Enter Scope: %s" scp.id
            scp :: env.path // extend current qname 
               
        let private enterAnonymousInnerScope env =
            let scope = Scope.createAnonymous ()
            // printfn "Enter Scope: %s" scope.id
            scope :: env.path
        
        // TODO: add scope as symbol and inner scope, fg 01.10.20
        let enterModuleScope (env: Environment) (id: Identifier) : Environment =
            // TODO: Fully qualified names (for code generation) require whole module name - not only the last id
            // 
            // let basicId = ""
            { env with path = [ Scope.createGlobalScope ()] }

        let enterOpenScope env (name: Name) : Environment = 
            { env with path = enterInnerScope env name.id Visibility.Open Recursion.No }

        let enterClosedScope env (name: Name) : Environment =
            { env with path = enterInnerScope env name.id Visibility.Closed Recursion.No }

        let enterAnonymousScope env : Environment =
            { env with path = enterAnonymousInnerScope env }

        // makes current scope recursive
        let enableRecursiveCurrentScope env : Environment =
            let recursiveCurrent = { currentScope env with recursion = Recursion.Yes }
            { env with path = recursiveCurrent :: currentOuter env }

        /// Leaving a scope means removing the current scope from the stack and
        /// putting it as an inner scope in its parent scope (which becomes the
        /// new stack top)
        let exitInnerScope (env: Environment) =
            assert (List.length env.path >= 1) // at least GlobalScope
            match env.path with
            | [globalscope] ->
                // printfn "Exit Scope: %s" globalscope.id
                { env with path = [] }// leaving the global scope
            | current :: parent :: outer ->
                // printfn "Exit Scope: %s" current.id
                { env with path = Scope.addInnerScope parent current :: outer } 
            | [] ->
                failwith "this should never happen"

        let findNameInCurrentScope env (name: Name) : Result<Environment, NameCheckError> =
            match Scope.tryFindSymbol (currentScope env) name.id with
            | Some symb ->
                let declName = symb.name
                do env.lookupTable.addUsage name declName
                Ok env
            | None ->
                Result.Error (NoDeclaration name)

        
        /// name checks a static access path
        /// updates the environment 
        
        let findCompletePath env (spath : AST.StaticNamedPath) : Result<Environment, NameCheckError> = 
            
            let rec findInnerDecls (decls: Name list) (scope: Scope) (path: Name list) : Name list = 
                match path with
                | [] -> 
                    decls

                | [name] ->
                    match Scope.tryFindSymbol scope name.id with
                    | None -> 
                        decls
                    | Some symbol ->
                        let declName = symbol.name
                        decls @ [declName]

                | name :: tail ->
                    match Scope.tryFindInnerScope scope name.id with
                    | None ->
                        decls
                    | Some innerscope ->
                        let declName = (Scope.getSymbol scope name.id).name
                        findInnerDecls  (decls @ [declName]) innerscope tail
            
            let findDecls (path: Name list) : Name list =
                let firstName = List.head path
                match tryFindDeclarationScope env firstName.id with   
                | None ->
                    []
                | Some declScope -> 
                    findInnerDecls [] declScope path     
            
            let path = spath.names
            let decls = findDecls path
            
            do List.iter2 env.lookupTable.addUsage <| List.take decls.Length path <| decls

            let isOk = decls.Length = path.Length 
            if isOk then
                Ok env
            elif path.Length = 1 then
                Error (NoDeclaration path.[0])
            else
                Error (NoDeclarationInStaticAccess (path.[decls.Length], spath))


        /// name check the static part of dynamic access path 
        /// updates the environment with a list of used names
        /// returns declaration name or an error
        
        let findPartialPath env (dpath: AST.DynamicAccessPath) : Result< Environment, NameCheckError > =   // we use array for better error messages
            
            let rec probeInnerDecls (decls: Name list) (scope: Scope) (path: Name list) = 
                match path with
                | [] ->
                    decls, true
                | [name] ->
                    match Scope.tryFindSymbol scope name.id with
                    | None -> 
                        decls, false
                    | Some symbol ->
                        decls @ [symbol.name], true
                | name :: tail ->
                    match Scope.tryFindSymbol scope name.id with
                    | None ->
                        decls, false
                    | Some symbol ->
                        match Scope.tryFindInnerScope scope name.id with
                        | None ->
                            if symbol.isScope then 
                                decls, false
                            else
                                decls @ [symbol.name], true
                        | Some innerscope ->
                            probeInnerDecls ( decls @ [symbol.name] ) innerscope tail
                     
            let findDecls (path: Name list) =
                let firstName = List.head path
                match tryFindDeclarationScope env firstName.id with
                | None ->
                    [], false
                | Some declScope -> 
                    probeInnerDecls [] declScope path     
           
            let path = dpath.leadingNames
            let decls, isOk = findDecls path
             
            do List.iter2 env.lookupTable.addUsage <| List.take decls.Length path <| decls

            if isOk then 
                Ok env // preliminary eliminate this
            elif path.Length = 1 then
                Error (NoDeclaration (path.[0]))
            else
                Error (NoDeclarationInDynamicAccess (path.[decls.Length], dpath))

        /// name checks an impliit member access
        /// i.e. a static access path without (currently?) one qualifying names
        /// updates the environment with the name usages
        /// returns declaration name or an error

        let findImplicitPath (env: Environment) (implicitMember: AST.StaticNamedPath) : Result<Environment, NameCheckError> =
            
            // on success returns a list of declaration names
            // in case of failure an empty list
            // declsAcc starts with a guessed declaration
            // returns accumulate declaration names
            let rec probeInnerDecl (declsAcc: Name list) (scope: Scope) (dotpath: Name list) : Name list = 
                match dotpath with
                | [name] ->
                    match Scope.tryFindSymbol scope name.id with
                    | None ->
                        []
                    | Some symb ->
                        declsAcc @ [symb.name]
                | name :: tail ->
                    match Scope.tryFindInnerScope scope name.id with
                    | None ->
                        []
                    | Some innerscope ->
                        let symb = Scope.getSymbol scope name.id
                        probeInnerDecl (declsAcc @ [symb.name]) innerscope tail
                | [] -> 
                    failwith "Implicit member path should never be empty"
            
            let dotpath = implicitMember.names

            let probeInnerScopes (scope: Scope) : Name list list =
                let openInnerScopes = Map.fold
                                        (fun oiss _ s -> if s.visibility = Visibility.Open then oiss @ [s] else oiss) 
                                        [] scope.innerscopes
                
                let declName innerscope = (Scope.getSymbol scope innerscope.id).name 
                
                List.map (fun (ois: Scope) -> probeInnerDecl [declName ois] ois dotpath) openInnerScopes
                |> List.filter (List.isEmpty >> not) 
                
            // accumulates possible declarations
            let rec probeScopes (positives: Name list list) (path: Scope list) =
                match path with
                | [] ->
                    failwith "scope stack should never be empty"
                | [globalscope] ->
                    positives @ probeInnerScopes globalscope
                | current :: outer ->
                    let innerPositives = probeInnerScopes current
                    probeScopes (positives @ innerPositives) outer
            
            match probeScopes [] env.path with
            | [] ->
                Error (NoImplicitMemberDeclaration implicitMember) 
            | [decl] ->
                do List.iter2 env.lookupTable.addUsage dotpath (List.tail decl)
                Ok env
            | decls -> 
                Error (NonUniqueImplicitMember (implicitMember, decls))

