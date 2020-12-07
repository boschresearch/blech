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

    type Singleton = 
    | OpaqueSingleton
    | Singleton of calledSingletons: Name list


    type AbstractType =
    | Type
    | SimpleType


    type ExportContext = 
        private {
            Environment : SymbolTable.Environment
            Logger : Diagnostics.Logger
            AbstractTypes : Map<Name, AbstractType> 
            Singletons : Map<Name, Singleton>
            ExportScope : SymbolTable.Scope
        }

        static member Initialise (logger: Diagnostics.Logger) (env: SymbolTable.Environment) = 
            { 
                Environment = env
                Logger = logger
                AbstractTypes = Map.empty
                Singletons = Map.empty
                ExportScope = SymbolTable.Scope.createExportScope ()
            }

        member this.TryGetAbstractType name =
            this.AbstractTypes.TryFind name

        member this.TryGetSingleton name = 
            this.Singletons.TryFind name

        member this.IsExposed name = 
            Env.isExposedName this.Environment name

        member this.GetExports = 
            this.ExportScope

        member this.Show = 
            for n in this.Singletons do
                printfn "Singleton: %A Info: %A" n.Key n.Value
            for n in this.AbstractTypes do
                printfn "Abstract Type : %A Value: %A" n.Key n.Value
            printfn "Exports: %A" this.ExportScope
            

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
        do Diagnostics.Logger.logError ctx.Logger Diagnostics.Phase.Exports err
        ctx



    // begin ==========================================
    // recursively descend the AST for export inference

    let private inferStaticNamedPath ctx (snp: AST.StaticNamedPath) = 
        ctx

    let private inferDynamicNamePath ctx (dap: AST.DynamicAccessPath) =
        ctx

    let private inferImplicitMember ctx (snp: AST.StaticNamedPath) = 
        ctx

    let private inferNameInCurrentScope ctx (sharing: Name) = 
        ctx


    let private exportValueDecl (ctx: ExportContext) (name: Name) =
        if ctx.IsExposed name then
            let expScp = Env.exportName ctx.Environment name ctx.ExportScope
            { ctx with ExportScope = expScp }
        else
            ctx


    let private exportProcedureDecl (ctx: ExportContext) (name: Name) =
        if ctx.IsExposed name then
            let expScp = Env.exportName ctx.Environment name ctx.ExportScope
            { ctx with ExportScope = expScp }
        else
            ctx


    let private exportTypeDecl (ctx: ExportContext) (name: Name) =
        match ctx.IsExposed name, ctx.TryGetAbstractType name with
        | false, Some _ -> // add abstract type to export scope
            let expScp = Env.exportName ctx.Environment name ctx.ExportScope
            { ctx with ExportScope = expScp }
        | true, None -> // add concrete type to export scope
            let expScp = Env.exportName ctx.Environment name ctx.ExportScope
                         |> Env.exportScope ctx.Environment name
            { ctx with ExportScope = expScp }
        | false, None ->
            ctx
        | true, Some _ -> 
            failwith "Exposed type can never become an abstract type"

    let private exportModuleScope (ctx: ExportContext) =
        let modScp = Env.getModuleScope ctx.Environment
        { ctx with ExportScope = modScp }

    let rec private inferUnitExpr ctx (ue: AST.UnitExpr) = 
        match ue with
        | UnitExpr.One _ ->
            ctx
        | UnitExpr.Parens (ue, _) ->
            inferUnitExpr ctx ue
        | UnitExpr.Unit sname ->
            inferStaticNamedPath ctx sname 
        | UnitExpr.UnitExp (ue, _, _) ->
            inferUnitExpr ctx ue
        | UnitExpr.UnitDiv (uel, uer)
        | UnitExpr.UnitMul (uel, uer) ->
            inferUnitExpr ctx uel 
            |> inferUnitExpr <| uer
 
    
    let private inferLiteral ctx (lit: AST.Literal) = // infered because of units
        match lit with
        | Literal.Float (unit = ue)
        | Literal.Int (unit = ue) ->
            Option.fold inferUnitExpr ctx ue
        | _ ->
            ctx


    let rec private inferCode ctx (c: AST.Code) =
        match c with
        | Code.Procedure fp   // will be dynamic with function pointers
            -> inferDynamicAccessPath ctx fp


    and private inferStructField ctx field = 
        inferExpr ctx field.expr


    and private inferArrayField ctx field =
        Option.fold inferExpr ctx field.index
        |> inferExpr <| field.value


    and private inferAccess ctx (acc: AST.Access) =
        match acc with
        | Index (index = e)
        | StaticIndex (index = e) ->
            inferExpr ctx e
        | _ ->
            ctx    


    and private inferDynamicAccessPath ctx (dPath: AST.DynamicAccessPath) =
        List.fold inferAccess ctx dPath.path
        |> inferDynamicNamePath <| dPath


    and private inferExpr ctx (exp: AST.Expr) =
        match exp with
        | Expr.Const lit ->
            inferLiteral ctx lit
        | Expr.AggregateConst (fieldExpr, _) ->
            match fieldExpr with
            | ResetFields -> ctx
            | StructFields fields -> List.fold inferStructField ctx fields
            | ArrayFields fields -> List.fold inferArrayField ctx fields
        | Expr.SliceConst _ ->
            ctx
        | Expr.ImplicitMember name ->
            inferImplicitMember ctx name
        | Expr.Var pname ->
            inferDynamicAccessPath ctx pname
        | Expr.Not (e, _) 
        | Expr.Bnot (e, _)
        | Expr.Unm (e, _) 
        | Expr.Len (e, _)
        | Expr.Cap (e, _)
        | Expr.Parens (e, _) ->
            inferExpr ctx e
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
            |> inferExpr <| s1 
            |> inferExpr <| s2
        | Convert (expr, dty, _) 
        | HasType (expr, dty) ->
            ctx 
            |> inferExpr <| expr
            |> inferDataType <| dty
        | Expr.FunctionCall (fp, inputs, outputs, _) ->
            ctx
            |> inferCode <| fp
            |> List.fold inferExpr <| inputs
            |> List.fold inferDynamicAccessPath <| outputs


    and private inferDataType ctx (dt: AST.DataType) =
        match dt with
        | BoolType _
        | BitvecType _ ->
            ctx
        | NaturalType (unit = uexp)
        | IntegerType (unit = uexp) 
        | FloatType (unit = uexp) ->
            Option.fold inferUnitExpr ctx uexp
        | ArrayType (size = expr; elem = dty) ->
            // resumeExposure ctx
            inferExpr ctx expr
            // |> disableExposure
            |> inferDataType <| dty
        | SliceType (elem = dty) ->
            inferDataType ctx dty
        | TypeName snp ->
            inferStaticNamedPath ctx snp
        | Signal (value = dt) ->
            Option.fold inferDataType ctx dt
  
  

    let private inferParamDecl ctx (pd: AST.ParamDecl) = 
        List.fold inferNameInCurrentScope ctx pd.sharing
        |> inferDataType <| pd.datatype


    let private inferReturnDecl ctx (rd: AST.ReturnDecl) = 
        List.fold inferNameInCurrentScope ctx rd.sharing
        |> inferDataType <| rd.datatype
 
 
    let private inferVarDecl ctx (vd: AST.VarDecl) =
        Option.fold inferDataType ctx vd.datatype
        |> Option.fold inferExpr <| vd.initialiser


    let private inferStaticVarDecl ctx (vd: AST.VarDecl) = 
        Option.fold inferDataType ctx vd.datatype
        |> Option.fold inferExpr <| vd.initialiser
        |> exportValueDecl <| vd.name


    let private inferLocation ctx (lhs: AST.Receiver) =
        match lhs with
        | AST.Location (Loc l) -> 
            inferDynamicAccessPath ctx l
        | AST.FreshLocation vd ->
            Option.fold inferDataType ctx vd.datatype
        | _ ->
            ctx


    let private inferCondition ctx (cond: AST.Condition) =
        match cond with
        | Condition.Cond e ->
            inferExpr ctx e
        | Condition.SignalBinding ob ->
            inferVarDecl ctx ob 
        | Condition.Tick (spath, _) ->
            inferStaticNamedPath ctx spath
  
  
    let rec private inferStatement ctx (stmt: AST.Stmt) =
        match stmt with
        | LocalVar vdecl ->
            inferVarDecl ctx vdecl
            //Option.fold inferDataType ctx vdecl.datatype
            //|> Option.fold inferExpr <| vdecl.initialiser
            //|> addDecl <| vdecl

        | Assign (_, lhs, rhs) ->
            match lhs with
            | AST.Wildcard _ -> ctx
            | AST.Loc l -> inferDynamicAccessPath ctx l
            
            |> inferExpr <| rhs

        | Assert (_, conds, msg) ->
            List.fold inferCondition ctx conds
            |> Option.fold inferExpr <| msg

        | Assume (_, conds, msg) ->
            List.fold inferCondition ctx conds
            |> Option.fold inferExpr <| msg

        | Await (_, conds) ->
            List.fold inferCondition ctx conds

        // TODO: Rather inelegant, can this be improved in the AST, fjg 02.08.2018 
        | ITE (_, conds, bodyIf, (bodyElse, isElseIf)) ->
            List.fold inferCondition ctx conds
            |> List.fold inferStatement <| bodyIf
            |> List.fold inferStatement <| bodyElse

        | Cobegin (_, blockList) ->
            let chkBlock ctx (_, stmts) =           // ignore strength
                List.fold inferStatement ctx stmts
            List.fold chkBlock ctx blockList

        | WhileRepeat (_, conds, body) ->
            List.fold inferCondition ctx conds
            |> List.fold inferStatement <| body

        | RepeatUntil (_, body, conds) ->
            List.fold inferStatement ctx body
            |> List.fold inferCondition <| conds    // options bindings only visible in 'until' conditions

        | NumericFor (_, var, init, limit, step, body) ->
            inferExpr ctx init
            |> inferExpr <| limit
            |> Option.fold inferExpr <| step
            |> inferVarDecl <| var                  // loop var only visible inside loop
            |> List.fold inferStatement <| body 

        | IteratorFor (_, var, _, iterable, body) -> 
            inferExpr ctx iterable
            |> inferVarDecl <| var                  // loop var only visible inside loop
            |> List.fold inferStatement <| body 

        | Preempt (_, _, conds, _, body) ->            
            List.fold inferCondition ctx conds      // option bindings not visible inside body
            |> List.fold inferStatement <| body

        | Stmt.SubScope (_, body) ->
            List.fold inferStatement ctx body

        | ActivityCall (_, optReceiver, ap, inputs, outputs) -> 
            // fresh location added to scope last, 'run let x = Activity(x)' should be wrong
            inferCode ctx ap
            |> List.fold inferExpr <| inputs
            |> List.fold inferDynamicAccessPath <| outputs
            |> Option.fold inferLocation <| optReceiver 

        | FunctionCall (_, fp, inputs, outputs) ->
            inferCode ctx fp
            |> List.fold inferExpr <| inputs
            |> List.fold inferDynamicAccessPath <| outputs

        | Emit (_, receiver, optExpr) ->
            // fresh location added to scope last, 'emit let x = x + 1' should be wrong
            Option.fold inferExpr ctx optExpr 
            |> inferLocation <| receiver

        | Return (_, expr) ->
            Option.fold inferExpr ctx expr 
        
        | Pragma _ 
        | Nothing ->
            ctx
 
 
    let private inferSubprogram ctx (sp: AST.SubProgram) =
        List.fold inferParamDecl ctx sp.inputs
        |> List.fold inferParamDecl <| sp.outputs
        |> Option.fold inferReturnDecl <| sp.result
        |> List.fold inferStatement <| sp.body
        |> exportProcedureDecl <| sp.name


    let private inferFunctionPrototype ctx (fp: Prototype) =
        List.fold inferParamDecl ctx fp.inputs
        |> List.fold inferParamDecl <| fp.outputs
        |> Option.fold inferReturnDecl <| fp.result
        |> exportProcedureDecl <| fp.name


    let private inferUnitDecl ctx (ud: AST.UnitDecl) =
        exportValueDecl ctx ud.name

 
    let private inferTagDecl ctx (td: AST.TagDecl) =
        Option.fold inferExpr ctx td.rawvalue
        

    // all field names are syntactically var decls
    let private inferFieldDecl ctx (field: AST.Member) =
        match field with
        | Member.Var fdecl ->    
            Option.fold inferDataType ctx fdecl.datatype
            |> Option.fold inferExpr <| fdecl.initialiser
        | _ -> // other members do no occur as fields
            ctx

    let private inferImport ctx (import: AST.Import) = 
        ctx

    let rec private inferEnumType ctx (etd: AST.EnumTypeDecl) =
        Option.fold inferDataType ctx etd.rawtype   // infer rawtype first 
        |> List.fold inferTagDecl <| etd.tags
        |> List.fold inferMember <| etd.members
        |> exportTypeDecl <| etd.name


    and private inferStructType ctx (std: AST.StructTypeDecl) =
        List.fold inferFieldDecl ctx std.fields  // infer fields first, before typename becomes visible  
        |> List.fold inferMember <| std.members
        |> exportTypeDecl <| std.name


    and private inferOpaqueType ctx (ntd: AST.OpaqueTypeDecl) =
        List.fold inferMember ctx ntd.members
        |> exportTypeDecl <| ntd.name


    and private inferTypeAlias ctx (tad: AST.TypeAliasDecl) =
        inferDataType ctx tad.aliasfor          // infer alias first, before typename becomes visible
        |> List.fold inferMember <| tad.members
        |> exportTypeDecl <| tad.name


    and private inferMember ctx (m: AST.Member) =
        match m with
        | Member.EnumType et ->
            inferEnumType ctx et
        | Member.StructType st ->
            inferStructType ctx st
        | Member.OpaqueType nt ->
            inferOpaqueType ctx nt
        | Member.TypeAlias ta -> 
            inferTypeAlias ctx ta
        | Member.Var vdecl ->
            inferStaticVarDecl ctx vdecl
        | Member.Subprogram sp ->
            inferSubprogram ctx sp
        | Member.Prototype fp ->
            inferFunctionPrototype ctx fp
        | Member.Unit u ->
            inferUnitDecl ctx u
        | Member.Clock _ ->
            ctx //TODO
        | Member.Pragma _->
            ctx 
        | Member.Nothing -> 
            ctx
    
    
    
    // ModuleSpec 
    let private inferExposingAll ctx (exposing: AST.Exposing) = 
        match exposing with
        | AST.Few _->
            ctx
        | AST.All _ ->
            exportModuleScope ctx


    let private inferModuleSpecLast ctx (modSpec: AST.ModuleSpec) = 
        Option.fold inferExposingAll ctx modSpec.exposing


    // Imports
    //let private inferImportExposing ctx (exposing: AST.Exposing) = 
    //    match exposing with
    //    | AST.Few (names, _) ->
    //        List.fold (addDeclaration Import) ctx names
    //    | AST.All _ -> // TODO: add all exposed names from imported modules
    //        failwith "Remove wildcard '...' completely"
            
    //let private inferImport ctx (import: AST.Import) = 
    //    ctx

        //addDeclaration Import ctx import.localName
        //|> Option.fold inferImportExposing <| import.exposing


    // Compilation Unit
    let private inferCompilationUnit (ctx: ExportContext) (cu: AST.CompilationUnit) =
        if cu.IsModule  then 
            //List.fold inferImport ctx cu.imports
            List.fold inferMember ctx cu.members
            |> Option.fold inferModuleSpecLast <| cu.spec  // export all after 
        else
            ctx
            // logExportError ctx <| Dummy (cu.Range, "Test error for non-module")

    // end =========================================

    let inferExports logger (env: SymbolTable.Environment) (cu: AST.CompilationUnit) = 
        let ctx = ExportContext.Initialise logger env
        let exports = inferCompilationUnit ctx cu
        // just for debugging
        // show exports
        if Diagnostics.Logger.hasErrors exports.Logger then
            Error exports.Logger
        else
            Ok exports