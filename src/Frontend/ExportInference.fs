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


    type ToplevelType =
        | Complex
        | Simple


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
            // prev_visibility : Visibility 
            visibility : Visibility
            calledSingletons : Name list 
        }

        /// Exposing state for const, param, clock, unit
        static member Value env name  = 
            let vb = if Env.isExposedToplevelMember env name then Transparent else Invisible
            { topLevelMember = name 
              visibility = vb 
              calledSingletons = [] }
                   
        /// Exposing state for types, functions, activities, prototypes
        static member Type env name =
            let vb = if Env.isExposedToplevelMember env name then Semitransparent else Invisible
            { topLevelMember = name 
              visibility = vb 
              calledSingletons = [] }
            
        member this.StrengthenVisibility =
            { this with visibility = this.visibility.Strengthen }
        //    { this with visibility = visibility    | 

        member this.WeakenVisibility = 
            { this with visibility = this.visibility.Weaken }

        member this.AddCalledSingleton name = 
            { this with calledSingletons = name :: this.calledSingletons }
        

    type ExportContext = 
        private {
            environment : SymbolTable.Environment
            logger : Diagnostics.Logger
            abstractTypes : Map<Name, ToplevelType> 
            singletons : Map<Name, Singleton>
            exportScope : SymbolTable.Scope
        }

        static member Initialise (logger: Diagnostics.Logger) (env: SymbolTable.Environment) = 
            { 
                environment = env
                logger = logger
                // currentMember = Internal
                // state = State.Empty
                // currentVisibility = Hidden
                abstractTypes = Map.empty 
                singletons = Map.empty  // TODO: initialise with imported singletons, fjg. 8.12.20
                exportScope = SymbolTable.Scope.createExportScope ()
            }

        member this.AddAbstractType name abstype = 
            { this with abstractTypes = this.abstractTypes.Add (name, abstype) }

        member this.TryGetAbstractType name =
            this.abstractTypes.TryFind name

        member this.TryGetSingleton name = 
            this.singletons.TryFind name

        member this.IsExposedToplevelMember name = 
            Env.isExposedToplevelMember this.environment name

        member this.IsHiddenToplevelMember name = 
            Env.isHiddenToplevelMember this.environment name

        member this.IsHiddenImplicitMember name =
            Env.isHiddenImplicitMember this.environment name

        member this.GetDeclName name =
            Env.getDeclName this.environment name

        //member this.IsExposedName name = 
        //    Env.isExposedName this.environment name

        member this.GetExports = 
            this.exportScope


       
        member this.Show = 
            for n in this.singletons do
                printfn "Singleton: %A Info: %A" n.Key n.Value
            for n in this.abstractTypes do
                printfn "Abstract Type : %A Value: %A" n.Key n.Value
            printfn "Exports: %A" this.exportScope
            

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

    let private exportValueDecl (ctx: ExportContext) (name: Name) =
        if ctx.IsExposedToplevelMember name then
            let expScp = Env.exportName ctx.environment name ctx.exportScope
            { ctx with exportScope = expScp }
        else
            ctx


    let private exportProcedureDecl (ctx: ExportContext) (name: Name) =
        if ctx.IsExposedToplevelMember name then
            let expScp = Env.exportName ctx.environment name ctx.exportScope
            { ctx with exportScope = expScp }
        else
            ctx


    let private exportTypeDecl topLevelType (ctx: ExportContext) (name: Name) =
        if ctx.IsExposedToplevelMember name then 
            let expScp = Env.exportName ctx.environment name ctx.exportScope
                         |> Env.exportScope ctx.environment name
            { ctx with exportScope = expScp }
        else
            printfn "Add abstract type: %s" name.id
            ctx.AddAbstractType name topLevelType // will be exported if needed
        
    let private exportModuleScope (ctx: ExportContext) =
        let modScp = Env.getModuleScope ctx.environment
        { ctx with exportScope = modScp }


    let private exportIfAbstractType (ctx: ExportContext) (name: Name) =
        let declName = ctx.GetDeclName name
        match ctx.TryGetAbstractType declName with
        | Some _ ->
            let expScp = Env.exportName ctx.environment declName ctx.exportScope
            { ctx with exportScope = expScp }
        | _ ->
            ctx


    let private checkTransparentStaticName exp (ctx: ExportContext) (name: Name) = 
        let declName = ctx.GetDeclName name
        if ctx.IsHiddenToplevelMember declName then
            Dummy (name.Range, sprintf "Name '%s' is less accessible than declaration '%s'" name.id exp.topLevelMember.id )
            |> logExportError ctx 
        else 
            ctx

    let private checkTransparentDynamicName exp (ctx: ExportContext) (name: Name) = 
        let declName = ctx.GetDeclName name
        if ctx.IsHiddenToplevelMember declName then
            Dummy (name.Range, sprintf "Name '%s' is less accessible than declaration '%s'" name.id exp.topLevelMember.id)
            |> logExportError ctx 
        else 
            ctx
        
    let private checkTransparentImplicitName exp (ctx: ExportContext) (name: Name) =
        let declName = ctx.GetDeclName name
        if ctx.IsHiddenImplicitMember declName then
            Dummy (name.Range, sprintf "Implicit name '.%s' is less accessible than declaration '%s'" name.id exp.topLevelMember.id)
            |> logExportError ctx 
        else 
            ctx


    let private inferStaticNamedPath exp ctx (snp: AST.StaticNamedPath) = 
        let firstName = List.head snp.names
        match exp.visibility with
        | Transparent ->
            checkTransparentStaticName exp ctx firstName
        | Semitransparent ->
            exportIfAbstractType ctx firstName
        | _ ->
            ctx

    let private inferDynamicNamePath exp ctx (dap: AST.DynamicAccessPath) =
        let firstName = List.head dap.leadingNames
        match exp.visibility with
        | Transparent ->
            checkTransparentDynamicName exp ctx firstName
        | _ ->
            ctx

    let private inferImplicitMember exp ctx (snp: AST.StaticNamedPath) = 
        let firstName = List.head snp.names
        match exp.visibility with
        | Transparent ->
            checkTransparentImplicitName exp ctx firstName
        | _ ->
            ctx

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
        |> exportValueDecl <| vd.name


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
            //Option.fold inferDataType ctx vdecl.datatype
            //|> Option.fold inferExpr <| vdecl.initialiser
            //|> addDecl <| vdecl

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

        // TODO: Rather inelegant, can this be improved in the AST, fjg 02.08.2018 
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
            |> List.fold (inferCondition exp)  <| conds    // options bindings only visible in 'until' conditions

        | NumericFor (_, var, init, limit, step, body) ->
            inferExpr exp ctx init
            |> inferExpr exp <| limit
            |> Option.fold (inferExpr exp) <| step
            |> inferVarDecl exp <| var                  // loop var only visible inside loop
            |> List.fold (inferStatement exp) <| body 

        | IteratorFor (_, var, _, iterable, body) -> 
            inferExpr exp ctx iterable
            |> inferVarDecl exp <| var                  // loop var only visible inside loop
            |> List.fold (inferStatement exp) <| body 

        | Preempt (_, _, conds, _, body) ->            
            List.fold (inferCondition exp) ctx conds      // option bindings not visible inside body
            |> List.fold (inferStatement exp) <| body

        | Stmt.SubScope (_, body) ->
            List.fold (inferStatement exp) ctx body

        | ActivityCall (_, optReceiver, ap, inputs, outputs) -> 
            // fresh location added to scope last, 'run let x = Activity(x)' should be wrong
            inferCode exp ctx ap
            |> List.fold (inferExpr exp) <| inputs
            |> List.fold (inferDynamicAccessPath exp) <| outputs
            |> Option.fold (inferLocation exp) <| optReceiver 

        | FunctionCall (_, fp, inputs, outputs) ->
            inferCode exp ctx fp
            |> List.fold (inferExpr exp) <| inputs
            |> List.fold (inferDynamicAccessPath exp) <| outputs

        | Emit (_, receiver, optExpr) ->
            // fresh location added to scope last, 'emit let x = x + 1' should be wrong
            Option.fold (inferExpr exp) ctx optExpr 
            |> inferLocation exp <| receiver

        | Return (_, expr) ->
            Option.fold (inferExpr exp) ctx expr 
        
        | Pragma _ 
        | Nothing ->
            ctx
 
 
    let private inferSubprogram (exp: Exposing) ctx (sp: AST.SubProgram) =
        let bodyExp = weakenVisibility exp sp
        List.fold (inferParamDecl exp) ctx sp.inputs
        |> List.fold (inferParamDecl exp) <| sp.outputs
        |> Option.fold (inferReturnDecl exp) <| sp.result
        |> List.fold (inferStatement bodyExp) <| sp.body   // do not weaken for compile-time functions
        |> exportProcedureDecl <| sp.name


    let private inferFunctionPrototype exp ctx (fp: Prototype) =
        List.fold (inferParamDecl exp) ctx fp.inputs
        |> List.fold (inferParamDecl exp) <| fp.outputs
        |> Option.fold (inferReturnDecl exp) <| fp.result
        |> exportProcedureDecl <| fp.name


    let private inferUnitDecl exp ctx (ud: AST.UnitDecl) =
        exportValueDecl ctx ud.name

 
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
        Option.fold (inferDataType exp) ctx etd.rawtype   // infer rawtype first 
        |> List.fold (inferTagDecl exp) <| etd.tags
        |> List.fold (inferExtensionMember exp)  <| etd.members
        |> exportTypeDecl Complex <| etd.name


    and private inferStructType exp ctx (std: AST.StructTypeDecl) =
        List.fold (inferFieldDecl exp) ctx std.fields  // infer fields first, before typename becomes visible  
        |> List.fold (inferExtensionMember exp) <| std.members
        |> exportTypeDecl Complex <| std.name


    and private inferOpaqueType exp ctx (ntd: AST.OpaqueTypeDecl) =
        List.fold (inferExtensionMember exp)  ctx ntd.members
        |> exportTypeDecl Complex <| ntd.name   // TODO: toplevel type should be encoded into the AST


    and private inferTypeAlias exp ctx (tad: AST.TypeAliasDecl) =
        let topLevelType = 
            match tad.aliasfor with
            | BoolType _ | BitvecType _ | NaturalType _ | IntegerType _ | FloatType _ -> Simple
            | _ -> Complex

        inferDataType exp ctx tad.aliasfor
        |> List.fold (inferExtensionMember exp) <| tad.members  // TODO: change this to something like inferMethod
        |> exportTypeDecl topLevelType <| tad.name


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
    let private inferImport ctx (import: AST.Import) = 
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


    // Compilation Unit
    let private inferCompilationUnit (ctx: ExportContext) (cu: AST.CompilationUnit) =
        if cu.IsModule  then 
            //List.fold inferImport ctx cu.imports
            List.fold inferTopLevelMember ctx cu.members
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
        if Diagnostics.Logger.hasErrors exports.logger then
            Error exports.logger
        else
            Ok exports