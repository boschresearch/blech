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
    
    
    type ToplevelType =
        | Complex
        | Simple
   
    type AbstractTypes = Map<Name, ToplevelType>
    
    type OpaqueSingletons = Set<Name> 

    type ExportContext = 
        private {
            environment : SymbolTable.Environment
            logger : Diagnostics.Logger
            
            abstractTypes : AbstractTypes
            opaqueSingletons : OpaqueSingletons 
            
            exportScope : SymbolTable.Scope
            requiredImports: Map<Identifier, Identifier option> // import mod "url" exposes member: "mod" -> None; "member" -> Some mod
        }

        static member Initialise (logger: Diagnostics.Logger) 
                                 (env: SymbolTable.Environment) 
                                 (importedAbstractTypes : AbstractTypes list)
                                 (importedSingeltons: OpaqueSingletons list) = 
            {   
                environment = env
                logger = logger
                
                abstractTypes = Map.concatWithOverride importedAbstractTypes 
                opaqueSingletons = Set.unionMany importedSingeltons
                
                exportScope = SymbolTable.Scope.createExportScope ()
                requiredImports = Map.empty
            }

        member this.AddAbstractType name abstype = 
            { this with abstractTypes = this.abstractTypes.Add (name, abstype) }

        member this.AddOpaqueSingleton name = 
            { this with opaqueSingletons = this.opaqueSingletons.Add name }

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

        member this.TryGetAbstractType name =
            let declName = Env.getDeclName this.environment name
            this.abstractTypes.TryFind declName

        member this.TryGetOpaqueSingleton name = 
            let declName = Env.getDeclName this.environment name
            if this.opaqueSingletons.Contains declName then
                Some declName
            else
                None
            
        member this.GetExports = 
            this.exportScope

        member this.GetAbstractTypes = 
            this.abstractTypes

        member this.GetSingletons = 
            this.opaqueSingletons

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

    let private exportValueDecl isSingleton (ctx: ExportContext) (name: Name) =
        if Env.isExposedToplevelMember ctx.environment name.id then
            let expScp = Env.exportName ctx.environment name.id ctx.exportScope
            { ctx with exportScope = expScp }
        elif isSingleton then
            printfn "Add opaque singleton: %s" name.id
            ctx.AddOpaqueSingleton name // will only be exported if actually used
        else
            ctx


    //let private exportProcedureDecl (ctx: ExportContext) (proc: AST.SubProgram) =
    //    let id = proc.name.id
    //    let isSingleton = proc.isSingleton
    //    if Env.isExposedToplevelMember ctx.environment id then
    //        let expScp = Env.exportName ctx.environment id ctx.exportScope
    //        { ctx with exportScope = expScp }
    //    elif isSingleton then
    //        printfn "Add singleton: %s" id
    //        ctx
    //    else
    //        ctx

    //let private exportPrototypeDecl (ctx: ExportContext) (proto: AST.Prototype) =
    //    let id = proto.name.id
    //    let isSingleton = proto.isSingleton
    //    if Env.isExposedToplevelMember ctx.environment id then
    //        let expScp = Env.exportName ctx.environment id ctx.exportScope
    //        { ctx with exportScope = expScp }
    //    elif isSingleton then
    //        printfn "Add singleton: %s" id
    //        ctx
    //    else
    //        ctx

    let private exportTypeDecl topLevelType (ctx: ExportContext) (name: Name) =
        if Env.isExposedToplevelMember ctx.environment name.id then 
            let expScp = Env.exportName ctx.environment name.id ctx.exportScope
                         |> Env.exportScope ctx.environment name.id
            { ctx with exportScope = expScp }
        else
            printfn "Add abstract type: %s" name.id
            ctx.AddAbstractType name topLevelType // will only be exported if actually used

        
    let private exportAllTypesAndValues (ctx: ExportContext) =
        let modScp = Env.getModuleScope ctx.environment
        { ctx with exportScope = modScp }


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


    let private exportNameIfAbstractType (ctx: ExportContext) (name: Name) =
        match ctx.TryGetAbstractType name with
        | Some _ ->
            let expScp = Env.exportName ctx.environment name.id ctx.exportScope
            { ctx with exportScope = expScp }
        | _ ->
            ctx

    let private exportNameIfOpaqueSingleton (ctx: ExportContext) (name: Name) =
        match ctx.TryGetOpaqueSingleton name with
        | Some _ ->
            let expScp = Env.exportName ctx.environment name.id ctx.exportScope
            { ctx with exportScope = expScp }
        | _ ->
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
            |> exportNameIfOpaqueSingleton <| firstName
            |> requireImportIfImported <| firstName
        | _ ->
            ctx

    let private inferDynamicNamePath exp ctx (dap: AST.DynamicAccessPath) =
        let firstName = List.head dap.leadingNames
        match exp.visibility with
        | Transparent ->
            checkTransparentDynamicName exp ctx firstName
            |> requireImportIfImported <| firstName
        | _ ->
            ctx

    let private inferImplicitMember exp ctx (snp: AST.StaticNamedPath) = 
        let firstName = List.head snp.names
        match exp.visibility with
        | Transparent ->
            checkTransparentImplicitName exp ctx firstName
            |> requireImportForMemberIfImported <| firstName
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
        let topLevelType = 
            match tad.aliasfor with
            | BoolType _ | BitvecType _ | NaturalType _ | IntegerType _ | FloatType _ -> 
                Simple
            | TypeName snp ->
                match ctx.TryGetAbstractType (List.last snp.names) with
                | Some topLvTyp -> topLvTyp
                | None -> Complex
            | _ -> 
                Complex

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
    //let private inferImportExposing ctx (exposing: AST.Exposing) =
    //    // TODO: implement this here and in name checking
    //    ctx 

    //let private inferImport (ctx: ExportContext) (import: AST.Import) = 
    //    Option.fold inferImportExposing ctx import.exposing


    // ModuleSpec 
    let private inferExposingAll ctx (exposing: AST.Exposing) = 
        match exposing with
        | AST.Few _->
            ctx
        | AST.All _ ->
            exportAllTypesAndValues ctx


    let private inferModuleSpecLast ctx (modSpec: AST.ModuleSpec) = 
        Option.fold inferExposingAll ctx modSpec.exposing


    // Compilation Unit
    let private inferCompilationUnit (ctx: ExportContext) (cu: AST.CompilationUnit) =
        if cu.IsModule  then 
            ctx // List.fold inferImport ctx cu.imports
            |> List.fold inferTopLevelMember <| cu.members
            |> Option.fold inferModuleSpecLast <| cu.spec  // export all after 
        else
            ctx
            // logExportError ctx <| Dummy (cu.Range, "Test error for non-module")

    // end =========================================

    let inferExports logger (env: SymbolTable.Environment) 
                            (importedAbtractTypes : AbstractTypes list)
                            (importedSingletons : OpaqueSingletons list)
                            (cu: AST.CompilationUnit) =
        let exports =
            ExportContext.Initialise logger env importedAbtractTypes importedSingletons
            |> inferCompilationUnit <| cu
        // just for debugging
        printfn "Abstract Types: \n %A" exports.abstractTypes
        printfn "Singletons: \n %A" exports.opaqueSingletons
        printfn "Required imports: \n %A" exports.requiredImports
        if Diagnostics.Logger.hasErrors exports.logger then
            Error exports.logger
        else
            Ok exports