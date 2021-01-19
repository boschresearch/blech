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
    open CommonTypes
    open AST

    module Env = SymbolTable.Environment

    type private  Visibility =   
        | Invisible
        | Semitransparent
        | Transparent
        
        // needed for types that contain exposed expressions
        member this.Strengthen = 
            match this with
            | Transparent -> Transparent
            | Semitransparent -> Transparent
            | Invisible -> Invisible // once invisible always invisible

        // needed for functions that only expose the prototype
        member this.Weaken = 
            match this with
            | Transparent -> Transparent // once transparent always transparent
            | Semitransparent -> Invisible
            | Invisible -> Invisible

 
    type private Exposing =
        private { 
            topLevelMember : Name
            visibility : Visibility
        }

        /// Exposing state for const, param, clock, unit
        static member Value env name  = 
            let vb = if Env.isExposedToplevelMember env name.id then Transparent else Invisible
            { topLevelMember = name 
              visibility = vb }
                   
        /// Exposing state for types, functions, activities, prototypes
        static member Type env name =
            let vb = if Env.isExposedToplevelMember env name.id then Semitransparent else Invisible
            { topLevelMember = name 
              visibility = vb }
            
        member this.StrengthenVisibility =
            { this with visibility = this.visibility.Strengthen }

        member this.WeakenVisibility = 
            { this with visibility = this.visibility.Weaken }
    
    
    type AbstractType =
        | Complex
        | Simple
   
    type AbstractTypes = Map<Name, AbstractType>
    
    // type OpaqueSingletons = Set<Name> 

    type RequiredImports = Map<Identifier, Identifier option>

    // --- Singleton Handling

    type SingletonUsage = LongIdentifier list // in order of appearance

    type SingletonSignature = 
        | Opaque of SingletonUsage       // e.g. singleton [f, g] h
        | Translucent of SingletonUsage  // e.g. singleton [f, g] function h ()
    
    type SingletonSignatures = Map<Name, SingletonSignature>

    // --- Singleton handling
    
    //type private Path = Name list
     
    
    //type Singletons = 
    //    private {
    //        calledSingletons : Path list       // accumulator for called singletons in a subprogram
    //        singletons : Map<Name, Path list>  // declaration name |-> singleton uses (multiple occurences of the same singleton possible)
    //        signatures : Map<Name, SingletonSignature>
    //    }

    //    static member Empty = 
    //        { calledSingletons = List.empty
    //          singletons = Map.empty
    //          signatures = Map.empty }

    //    member this.AddCalledSingleton (env : SymbolTable.Environment) (path : Path) =
    //        assert this.IsSingleton env path
    //        { this with calledSingletons = path :: this.calledSingletons }  

    //    member this.HasCalledSingletons = 
    //        not <| List.isEmpty this.calledSingletons

    //    // Assume, that all called singletons have been collected
    //    //member this.AddSingleton declName =
    //    //    { this with 
    //    //        singletons = this.singletons.Add (declName, this.calledSingletons) 
    //    //        calledSingletons = List.empty }       

    //    member this.IsSingleton (env : SymbolTable.Environment) (path : Path) =
    //        let lastName = List.last path
    //        let declName = Env.getDeclName env lastName
    //        this.singletons.ContainsKey declName

    //    //member this.IsSingleton (declName : Name) =
    //    //    this.singletons.ContainsKey declName


    //    member private this.CalledToSignature : LongIdentifier list = 
    //        let pathToLongid path = List.map (fun name -> name.id) path
    //        this.calledSingletons
    //        |> List.map pathToLongid
    //        |> List.distinct

    //    //member this.AddTranslucentSingleton declName = 
    //    //    { calledSingletons = List.empty
    //    //      singletons = this.singletons.Add (declName, this.calledSingletons)
    //    //      signatures = this.signatures.Add (declName, Translucent this.CalledToSignature) }

    //    member this.AddSingleton declName signatureCase = 
    //        { calledSingletons = List.empty
    //          singletons = this.singletons.Add (declName, this.calledSingletons)
    //          signatures = this.signatures.Add (declName, signatureCase this.CalledToSignature) }


    //    member this.HasSignature declName =
    //        Option.isSome <| this.signatures.TryFind declName

    //    member this.GetSignature declName =
    //        this.signatures.Item declName

    //    member this.CollectSingletons (env : SymbolTable.Environment) declName : QName list =     
    //        let rec recurse path =
    //            let lastname = List.last path
    //            let declname = Env.getDeclName env lastname
    //            let qname = (Env.getLookupTable env).nameToQname declname
    //            match this.singletons.Item declname with
    //            | [] -> [qname]
    //            | singletons -> 
    //                qname :: List.collect recurse singletons

    //        List.collect recurse (this.singletons.Item declName)
    //        |> List.distinct


    type ExportContext = 
        private {
            logger : Diagnostics.Logger
            environment : SymbolTable.Environment
            singletons : SingletonInference.Singletons

            abstractTypes : AbstractTypes
            // opaqueSingletons : OpaqueSingletons 
            // singletons : Singletons
            
            exportScope : SymbolTable.Scope
            requiredImports: RequiredImports // import mod "url" exposes member: "mod" -> None; "member" -> Some mod
            singletonSignatures : SingletonSignatures
           
        }

        static member Initialise (logger: Diagnostics.Logger) 
                                 (env: SymbolTable.Environment) 
                                 (singletons: SingletonInference.Singletons)
                                 (importedAbstractTypes : AbstractTypes list) = 
                                 // (importedSingletons: SingletonInference.Singletons list) =
            {   
                // inputs
                environment = env
                logger = logger
                singletons = singletons
        
                // results
                abstractTypes = Map.collect importedAbstractTypes 
                exportScope = SymbolTable.Scope.createExportScope ()
                requiredImports = Map.empty
                singletonSignatures = Map.empty
                
            }

        //member this.AddAbstractType name abstype = 
        //    { this with abstractTypes = this.abstractTypes.Add (name, abstype) }

        //member this.AddOpaqueSingleton name = 
        //    { this with opaqueSingletons = this.opaqueSingletons.Add name }

        //member this.AddSingleton name =
        //    this.singletons.AddSingleton name

        member this.AddRequiredImports (id: Identifier) =
            if Env.isImportedName this.environment id then
                match Env.tryGetImportForMember this.environment id with
                | Some moduleId ->
                    { this with requiredImports = Map.add moduleId None this.requiredImports 
                                                  |> Map.add id (Some moduleId) }
                | None ->
                    { this with requiredImports = Map.add id None this.requiredImports }
            else
                this

        member this.IsAbstractType name = 
            let declName = Env.getDeclName this.environment name
            this.abstractTypes.ContainsKey declName

        //member this.IsOpaqueSingleton name = 
        //    let declName = Env.getDeclName this.environment name
        //    this.opaqueSingletons.Contains declName

        member this.TryGetAbstractType name =
            let declName = Env.getDeclName this.environment name
            this.abstractTypes.TryFind declName

        member this.HasOpaqueSingletonSignature name =
            let declName = Env.getDeclName this.environment name
            match this.singletonSignatures.TryFind declName with
            | Some (Opaque _) -> true
            | _ -> false
          
        member this.HasTranslucentSingletonSignature name = 
            let declName = Env.getDeclName this.environment name
            match this.singletonSignatures.TryFind declName with
            | Some (Translucent _) -> true
            | _ -> false
        
        member this.TryGetSingletonSignature declName = 
            assert Env.isDeclName this.environment declName
            // let declName = Env.getDeclName this.environment name
            this.singletonSignatures.TryFind declName

        member this.GetSingletonSignature declName = 
            assert Env.isDeclName this.environment declName
            // printfn "Singleton Signatures: %A" this.singletonSignatures
            this.singletonSignatures.Item declName

        member this.IsSingleton name = 
            if Env.isStaticName this.environment name then 
                let declName = Env.getDeclName this.environment name
                this.singletons.ContainsKey declName
            else
                false
        member this.AddSingletonSignature declName signatureTag =
            assert Env.isDeclName this.environment declName
            // printfn "Singletons: %A" this.singletons
            let singletonUses = this.singletons.Item declName // in reverse appearance order
            let pathsToLongids paths = List.map (fun name -> name.id) paths
            let longIds = 
                List.rev singletonUses  // to appearance order
                |> List.map pathsToLongids
                |> List.distinct
            let sss = this.singletonSignatures.Add (declName, signatureTag longIds)
            { this with singletonSignatures = sss }

        member this.IsExposed name  =
            Env.isExposedToplevelMember this.environment name.id
            
        member this.IsExported name = 
            SymbolTable.Scope.containsSymbol this.exportScope name.id

        member this.AddExport declName = 
            assert Env.isDeclName this.environment declName
            { this with exportScope = Env.exportName this.environment declName.id this.exportScope }

        member this.GetExports = 
            this.exportScope

        member this.GetAbstractTypes = 
            this.abstractTypes

        member this.GetSingletonSignatures = 
            this.singletonSignatures

        // TODO: remove this
        //member this.GetUsedSingletons declName = 
        //    assert Env.isDeclName this.environment declName
        //    match Map.tryFind declName this.singletonSignatures with
        //    | Some (Opaque usedSingletons)
        //    | Some (Translucent usedSingletons) ->
        //        usedSingletons
        //    | None ->
        //        List.empty

        
        member this.GetRequiredImports = 
            this.requiredImports

            
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


    // Helpers

    let private logExportError ctx err  = 
        do Diagnostics.Logger.logError ctx.logger Diagnostics.Phase.Exports err
        ctx

    let private strengthenVisibility (exp: Exposing) someAst =
        exp.StrengthenVisibility
    
    let private weakenVisibility (exp: Exposing) someAst =
        exp.WeakenVisibility
    
        
    // begin ==========================================
    // recursively descend the AST for export inference

    let private exportValueDecl isDeclaredSingleton (ctx: ExportContext) (name: Name) =
        // printfn "Export Value Decl: %s" name.id
        let isExposed = ctx.IsExposed name
        let isSingleton = ctx.IsSingleton name
        let addExport (ctx : ExportContext) name =
            if isExposed then 
                // printfn "Add exported value: %s" name.id
                ctx.AddExport name 
            else 
                ctx
        let addSingletonSignature (ctx : ExportContext) name = 
            if isSingleton && isExposed then 
                // printfn "Add translucent singleton: %s" name.id
                ctx.AddSingletonSignature name Translucent
            elif isSingleton then
                // printfn "Add opaque singleton: %s" name.id
                ctx.AddSingletonSignature name Opaque // will only be exported if actually used
            else 
                // printfn "IsSingleton is false: %s" name.id
                ctx 
                
        ctx 
        |> addExport <| name
        |> addSingletonSignature <| name


    let private exportTypeDecl abstractType (ctx: ExportContext) (name: Name) =
        if Env.isExposedToplevelMember ctx.environment name.id then 
            let expScp = Env.exportName ctx.environment name.id ctx.exportScope
                         |> Env.exportScope ctx.environment name.id
            { ctx with exportScope = expScp }
        else
            // printfn "Add abstract type: %s" name.id
            { ctx with abstractTypes = ctx.abstractTypes.Add(name, abstractType) } // will only be exported if actually used

        
    //let private exportAllTypesAndValues (ctx: ExportContext) =
    //    let modScp = Env.getModuleScope ctx.environment
    //    { ctx with exportScope = modScp }


    let private requireImportForMemberIfImported (ctx: ExportContext) (name: Name) =
        // printfn "try get import for member: %A" name
        match Env.tryGetImportForMember ctx.environment name.id with
        | Some declScopeId ->
            ctx.AddRequiredImports declScopeId
        | None ->
            ctx

    let private requireImportIfImported (ctx: ExportContext) (name: Name) =
        // printfn "require import for: %s" name.id
        ctx.AddRequiredImports name.id


    let private requireImportIfCalledSingleton (ctx: ExportContext) (name: Name) (maybeSingleton: Name) =
        // printfn "require import for: %s" name.id
        if ctx.IsSingleton maybeSingleton then 
            ctx.AddRequiredImports name.id
        else
            ctx


    let private exportNameIfAbstractType (ctx: ExportContext) (name: Name) =
        match ctx.TryGetAbstractType name with
        | Some _ ->
            let expScp = Env.exportName ctx.environment name.id ctx.exportScope
            { ctx with exportScope = expScp }
        | _ ->
            ctx

    let private exportNameIfOpaqueSingletonSignature (ctx: ExportContext) (name: Name) =
        if ctx.HasOpaqueSingletonSignature name then
            // printfn "Export opaque singleton: %s" name.id
            let expScp = Env.exportName ctx.environment name.id ctx.exportScope
            { ctx with exportScope = expScp }
        else    
            ctx

    let private checkTransparentStaticName exp (ctx: ExportContext) (name: Name) = 
        if Env.isHiddenToplevelMember ctx.environment name.id then
            Dummy (name.Range, sprintf "Name '%s' is less accessible than declaration '%s'" name.id exp.topLevelMember.id )
            |> logExportError ctx 
        else 
            ctx

    let private checkTransparentDynamicName exp (ctx: ExportContext) (name: Name) = 
        if Env.isHiddenToplevelMember ctx.environment name.id then
            Dummy (name.Range, sprintf "Name '%s' is less accessible than declaration '%s'" name.id exp.topLevelMember.id)
            |> logExportError ctx 
        else 
            ctx
        
    let private checkTransparentImplicitName exp (ctx: ExportContext) (name: Name) =
        if Env.isHiddenImplicitMember ctx.environment name.id then
            Dummy (name.Range, sprintf "Implicit name '.%s' is less accessible than declaration '%s'" name.id exp.topLevelMember.id)
            |> logExportError ctx 
        else 
            ctx


    let private inferStaticNamedPath exp ctx (snp: AST.StaticNamedPath) = 
        let firstName = List.head snp.names
        match exp.visibility with
        | Transparent ->
            checkTransparentStaticName exp ctx firstName
            |> requireImportIfImported <| firstName
        | Semitransparent ->
            exportNameIfAbstractType ctx firstName
            |> requireImportIfImported <| firstName
        | _ ->
            ctx


    let private inferDynamicNamePath exp ctx (dap: AST.DynamicAccessPath) =
        let firstName = List.head dap.leadingNames
        match exp.visibility with
        | Transparent ->
            checkTransparentDynamicName exp ctx firstName
            |> exportNameIfOpaqueSingletonSignature <| firstName
            |> requireImportIfImported <| firstName
        | _ ->
            let maybeImportedSingleton = List.last dap.leadingNames
            exportNameIfOpaqueSingletonSignature ctx firstName
            |> requireImportIfCalledSingleton <| firstName <| maybeImportedSingleton
            // ctx


    let private inferImplicitMember exp ctx (snp: AST.StaticNamedPath) = 
        let firstName = List.head snp.names
        match exp.visibility with
        | Transparent ->
            checkTransparentImplicitName exp ctx firstName
            |> exportNameIfOpaqueSingletonSignature <| firstName
            |> requireImportForMemberIfImported <| firstName
        | _ ->
            exportNameIfOpaqueSingletonSignature ctx firstName
            // ctx


    let private inferNameInCurrentScope exp ctx (sharing: Name) = 
        ctx
    
    let rec private inferUnitExpr exp ctx (ue: AST.UnitExpr) = 
        match ue with
        | UnitExpr.One _ ->
            ctx
        | UnitExpr.Parens (ue, _) ->
            inferUnitExpr exp ctx ue
        | UnitExpr.Unit sname ->
            inferStaticNamedPath exp ctx sname 
        | UnitExpr.UnitExp (ue, _, _) ->
            inferUnitExpr exp ctx ue
        | UnitExpr.UnitDiv (uel, uer)
        | UnitExpr.UnitMul (uel, uer) ->
            inferUnitExpr exp ctx uel 
            |> inferUnitExpr exp <| uer
 
    
    let private inferLiteral exp ctx (lit: AST.Literal) = // infered because of units
        match lit with
        | Literal.Float (unit = ue)
        | Literal.Int (unit = ue) ->
            Option.fold (inferUnitExpr exp) ctx ue
        | _ ->
            ctx


    let rec private inferCode exp ctx (c: AST.Code) =
        match c with
        | Code.Procedure fp   // will be dynamic with function pointers
            -> inferDynamicAccessPath exp ctx fp


    and private inferStructField exp ctx field = 
        inferExpr exp ctx field.expr


    and private inferArrayField exp ctx field =
        Option.fold (inferExpr exp) ctx field.index
        |> inferExpr exp <| field.value


    and private inferAccess exp ctx (acc: AST.Access) =
        match acc with
        | Index (index = e)
        | StaticIndex (index = e) ->
            inferExpr exp ctx e
        | _ ->
            ctx    


    and private inferDynamicAccessPath exp ctx (dPath: AST.DynamicAccessPath) =
        List.fold (inferAccess exp) ctx dPath.path
        |> inferDynamicNamePath exp <| dPath


    and private inferExpr exp ctx (expr: AST.Expr) =
        match expr with
        | Expr.Const lit ->
            inferLiteral exp ctx lit
        | Expr.AggregateConst (fieldExpr, _) ->
            match fieldExpr with
            | ResetFields -> ctx
            | StructFields fields -> List.fold (inferStructField exp) ctx fields
            | ArrayFields fields -> List.fold (inferArrayField exp) ctx fields
        | Expr.SliceConst _ ->
            ctx
        | Expr.ImplicitMember name ->
            inferImplicitMember exp ctx name
        | Expr.Var pname ->
            inferDynamicAccessPath exp ctx pname
        | Expr.Not (e, _) 
        | Expr.Bnot (e, _)
        | Expr.Unm (e, _) 
        | Expr.Len (e, _)
        | Expr.Cap (e, _)
        | Expr.Parens (e, _) ->
            inferExpr exp ctx e
        | Expr.And (s1, s2) 
        | Expr.Or (s1, s2)
        | Expr.Band (s1, s2) 
        | Expr.Bor (s1, s2) 
        | Expr.Bxor (s1, s2)
        | Expr.Shl (s1, s2)
        | Expr.Shr (s1, s2)
        | Expr.Sshr (s1, s2)
        | Expr.Rotl (s1, s2)
        | Expr.Rotr (s1, s2)
        | Expr.Eq (s1, s2)
        | Expr.Ieq (s1, s2)
        | Expr.Les (s1, s2)
        | Expr.Leq (s1, s2)
        | Expr.Grt (s1, s2)
        | Expr.Geq (s1, s2)
        | Expr.Ideq (s1, s2)
        | Expr.Idieq (s1, s2)
        | Expr.Add (s1, s2)
        | Expr.Sub (s1, s2)
        | Expr.Mul (s1, s2)
        | Expr.Div (s1, s2)
        | Expr.Mod (s1, s2)
        | Expr.Pow (s1, s2) ->
            ctx
            |> inferExpr exp <| s1 
            |> inferExpr exp <| s2
        | Convert (expr, dty, _) 
        | HasType (expr, dty) ->
            ctx 
            |> inferExpr exp <| expr
            |> inferDataType exp <| dty
        | Expr.FunctionCall (fp, inputs, outputs, _) ->
            ctx
            |> inferCode exp <| fp
            |> List.fold (inferExpr exp) <| inputs
            |> List.fold (inferDynamicAccessPath exp) <| outputs


    and private inferDataType exp ctx (dt: AST.DataType) =
        match dt with
        | BoolType _
        | BitvecType _ ->
            ctx
        | NaturalType (unit = uexp)
        | IntegerType (unit = uexp) 
        | FloatType (unit = uexp) ->
            Option.fold (inferUnitExpr exp) ctx uexp
        | ArrayType (size = expr; elem = dty) ->
            strengthenVisibility exp expr // always strength visibility for expr - a compile-time value-dependent type
            |> inferExpr <| ctx <| expr
            |> inferDataType exp <| dty
        | SliceType (elem = dty) ->
            inferDataType exp ctx dty
        | TypeName snp ->
            inferStaticNamedPath exp ctx snp
        | Signal (value = dt) ->
            Option.fold (inferDataType exp) ctx dt
  
  

    let private inferParamDecl exp ctx (pd: AST.ParamDecl) = 
        List.fold (inferNameInCurrentScope exp) ctx pd.sharing
        |> inferDataType exp <| pd.datatype


    let private inferReturnDecl exp ctx (rd: AST.ReturnDecl) = 
        List.fold (inferNameInCurrentScope exp) ctx rd.sharing
        |> inferDataType  exp <| rd.datatype
 
 
    let private inferVarDecl exp ctx (vd: AST.VarDecl) =
        Option.fold (inferDataType exp) ctx vd.datatype
        |> Option.fold (inferExpr exp) <| vd.initialiser


    let private inferStaticVarDecl exp ctx (vd: AST.VarDecl) =
        Option.fold (inferDataType exp) ctx vd.datatype
        |> Option.fold (inferExpr exp) <| vd.initialiser
        |> exportValueDecl false <| vd.name


    let private inferLocation exp ctx (lhs: AST.Receiver) =
        match lhs with
        | AST.Location (Loc l) -> 
            inferDynamicAccessPath exp ctx l
        | AST.FreshLocation vd ->
            Option.fold (inferDataType exp) ctx vd.datatype
        | _ ->
            ctx


    let private inferCondition exp ctx (cond: AST.Condition) =
        match cond with
        | Condition.Cond e ->
            inferExpr exp ctx e
        | Condition.SignalBinding ob ->
            inferVarDecl exp ctx ob 
        | Condition.Tick (spath, _) ->
            inferStaticNamedPath exp ctx spath
  
  
    let rec private inferStatement exp ctx (stmt: AST.Stmt) =
        match stmt with
        | LocalVar vdecl ->
            inferVarDecl exp ctx vdecl

        | Assign (_, lhs, rhs) ->
            match lhs with
            | AST.Wildcard _ -> ctx
            | AST.Loc l -> inferDynamicAccessPath exp ctx l
            
            |> inferExpr exp <| rhs

        | Assert (_, conds, msg) ->
            List.fold (inferCondition exp) ctx conds
            |> Option.fold (inferExpr exp) <| msg

        | Assume (_, conds, msg) ->
            List.fold (inferCondition exp) ctx conds
            |> Option.fold (inferExpr exp) <| msg

        | Await (_, conds) ->
            List.fold (inferCondition exp) ctx conds

        | ITE (_, conds, bodyIf, (bodyElse, isElseIf)) ->
            List.fold (inferCondition exp)  ctx conds
            |> List.fold (inferStatement exp) <| bodyIf
            |> List.fold (inferStatement exp) <| bodyElse

        | Cobegin (_, blockList) ->
            let chkBlock exp ctx (_, stmts) =           // ignore strength
                List.fold (inferStatement exp) ctx stmts
            List.fold (chkBlock exp) ctx blockList

        | WhileRepeat (_, conds, body) ->
            List.fold (inferCondition exp) ctx conds
            |> List.fold (inferStatement exp) <| body

        | RepeatUntil (_, body, conds) ->
            List.fold (inferStatement exp) ctx body
            |> List.fold (inferCondition exp)  <| conds

        | NumericFor (_, var, init, limit, step, body) ->
            inferExpr exp ctx init
            |> inferExpr exp <| limit
            |> Option.fold (inferExpr exp) <| step
            |> inferVarDecl exp <| var
            |> List.fold (inferStatement exp) <| body 

        | IteratorFor (_, var, _, iterable, body) -> 
            inferExpr exp ctx iterable
            |> inferVarDecl exp <| var
            |> List.fold (inferStatement exp) <| body 

        | Preempt (_, _, conds, _, body) ->            
            List.fold (inferCondition exp) ctx conds
            |> List.fold (inferStatement exp) <| body

        | Stmt.SubScope (_, body) ->
            List.fold (inferStatement exp) ctx body

        | ActivityCall (_, optReceiver, ap, inputs, outputs) -> 
            inferCode exp ctx ap
            |> List.fold (inferExpr exp) <| inputs
            |> List.fold (inferDynamicAccessPath exp) <| outputs
            |> Option.fold (inferLocation exp) <| optReceiver 

        | FunctionCall (_, fp, inputs, outputs) ->
            inferCode exp ctx fp
            |> List.fold (inferExpr exp) <| inputs
            |> List.fold (inferDynamicAccessPath exp) <| outputs

        | Emit (_, receiver, optExpr) ->
            Option.fold (inferExpr exp) ctx optExpr 
            |> inferLocation exp <| receiver

        | Return (_, expr) ->
            Option.fold (inferExpr exp) ctx expr 
        
        | Pragma _ 
        | Nothing ->
            ctx
 
 
    let private inferSubprogram (exp: Exposing) ctx (sp: AST.SubProgram) =
        let bodyExp = weakenVisibility exp sp
        List.fold (inferStaticNamedPath exp) ctx sp.singletons
        |> List.fold (inferParamDecl exp) <| sp.inputs
        |> List.fold (inferParamDecl exp) <| sp.outputs
        |> Option.fold (inferReturnDecl exp) <| sp.result
        |> List.fold (inferStatement bodyExp) <| sp.body   // do not weaken for compile-time functions
        |> exportValueDecl sp.isSingleton <| sp.name



    let private inferFunctionPrototype exp ctx (fp: Prototype) =
        List.fold (inferParamDecl exp) ctx fp.inputs
        |> List.fold (inferParamDecl exp) <| fp.outputs
        |> Option.fold (inferReturnDecl exp) <| fp.result
        |> exportValueDecl fp.isSingleton <| fp.name


    let private inferUnitDecl exp ctx (ud: AST.UnitDecl) =
        exportValueDecl false ctx ud.name

 
    let private inferTagDecl exp ctx (td: AST.TagDecl) =
        Option.fold (inferExpr exp) ctx td.rawvalue
        

    // all field names are syntactically var decls
    let private inferFieldDecl exp ctx (field: AST.Member) =
        match field with
        | Member.Var fdecl ->  
            let exp = Option.fold strengthenVisibility exp fdecl.initialiser // strengthen only if initialiser is present    
            Option.fold (inferDataType exp) ctx fdecl.datatype
            |> Option.fold (inferExpr exp) <| fdecl.initialiser
        | _ -> // other members do no occur as fields
            ctx

    let rec private inferEnumType exp ctx (etd: AST.EnumTypeDecl) =
        let rawExp = Option.fold strengthenVisibility exp etd.rawtype // raw types must not be abstract
        Option.fold (inferDataType rawExp) ctx etd.rawtype    
        |> List.fold (inferTagDecl rawExp) <| etd.tags  // raw values must not contain abstract types
        |> List.fold (inferExtensionMember exp)  <| etd.members
        |> exportTypeDecl Complex <| etd.name


    and private inferStructType exp ctx (std: AST.StructTypeDecl) =
        List.fold (inferFieldDecl exp) ctx std.fields  // infer fields first, before typename becomes visible  
        |> List.fold (inferExtensionMember exp) <| std.members
        |> exportTypeDecl Complex <| std.name


    and private inferOpaqueType exp ctx (ntd: AST.OpaqueTypeDecl) =
        List.fold (inferExtensionMember exp)  ctx ntd.members
        |> exportTypeDecl Complex <| ntd.name   // TODO: toplevel type should be encoded into the AST


    and private inferTypeAlias exp (ctx: ExportContext) (tad: AST.TypeAliasDecl) =
        let abstractType = 
            match tad.aliasfor with
            | BoolType _ | BitvecType _ | NaturalType _ | IntegerType _ | FloatType _ -> 
                Simple
            | TypeName snp ->
                match ctx.TryGetAbstractType (List.last snp.names) with
                | Some absTyp -> absTyp
                | None -> Complex
            | _ -> 
                Complex

        inferDataType exp ctx tad.aliasfor
        |> List.fold (inferExtensionMember exp) <| tad.members  // TODO: change this to something like inferMethod
        |> exportTypeDecl abstractType <| tad.name


    and private inferExtensionMember exp ctx (em: AST.Member) = 
        match em with
        | Member.TypeAlias ta ->
            inferTypeAlias exp ctx ta
        | Member.Var svd ->
            inferStaticVarDecl exp ctx svd
        | Member.Subprogram sp ->
            inferSubprogram exp ctx sp
        | Member.Prototype fp ->
            inferFunctionPrototype exp ctx fp
        | _ ->
            failwith "îllegal member in extension, this should have been excluded by the parser"


    let private inferTopLevelMember (ctx: ExportContext) (m: AST.Member) =
        match m with
        | Member.EnumType et ->
            let exp = Exposing.Type ctx.environment et.name
            inferEnumType exp ctx et
        | Member.StructType st ->
            let exp = Exposing.Type ctx.environment st.name
            inferStructType exp ctx st
        | Member.OpaqueType ot ->
            let exp = Exposing.Type ctx.environment ot.name
            inferOpaqueType exp ctx ot
        | Member.TypeAlias ta ->
            let exp = Exposing.Type ctx.environment ta.name
            inferTypeAlias exp ctx ta
        | Member.Var svd -> 
            let exp = Exposing.Value ctx.environment svd.name
            inferStaticVarDecl exp ctx svd
        | Member.Subprogram sp ->
            let exp = Exposing.Type ctx.environment sp.name
            inferSubprogram exp ctx sp
        | Member.Prototype fp ->
            let exp = Exposing.Type ctx.environment fp.name
            inferFunctionPrototype exp ctx fp
        | Member.OpaqueSingleton _ ->
            // only occurs in signatures
            ctx
        | Member.Unit u ->
            // inferUnitDecl ctx u
            ctx
        | Member.Clock _ ->
            ctx
        | Member.Pragma _->
            ctx 
        | Member.Nothing -> 
            failwith "this should have been removed"
        

    // Import
    //let private inferImportExposing ctx (exposing: AST.Exposing) =
    //    // TODO: implement this here
    //    ctx 

    //let private inferImport (ctx: ExportContext) (import: AST.Import) = 
    //    Option.fold inferImportExposing ctx import.exposing


    // ModuleSpec 
    //let private inferExposing ctx (exposing: AST.Exposing) = 
    //    ctx 
        

    //let private inferModuleSpecLast ctx (modSpec: AST.ModuleSpec) = 
    //    Option.fold inferExposing ctx modSpec.exposing


    // Compilation Unit
    let private inferCompilationUnit (ctx: ExportContext) (cu: AST.CompilationUnit) =
        if cu.IsModule  then 
            List.fold inferTopLevelMember ctx cu.members
        else
            ctx

    // end =========================================
    
    
    let inferExports logger (env: SymbolTable.Environment) 
                            (singletons: SingletonInference.Singletons)
                            (importedAbtractTypes : AbstractTypes list)
                            // (importedSingletons : SingletonInference.Singletons list)
                            (cu: AST.CompilationUnit) =
        let exports =
            ExportContext.Initialise logger env singletons importedAbtractTypes // importedSingletons
            |> inferCompilationUnit <| cu
        // just for debugging
        //printfn "Abstract Types: \n %A" exports.abstractTypes
        //printfn "SingletonSignatures: \n %A" exports.singletonSignatures
        //printfn "Required imports: \n %A" exports.requiredImports
        if Diagnostics.Logger.hasErrors exports.logger then
            Error exports.logger
        else
            Ok exports