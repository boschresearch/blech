﻿// Copyright (c) 2019 - for information on the respective copyright owner
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

// Design decisions
// make function parameters a separate subscope (Reason: previous checking)
// function f(params) block
// namedscope f :: anonymous scope (params) :: anonymous scope (block)


/// The goal of the identification of identifiers is to give every declaration
/// a fully qualified name and to point every use of a name to its declaration.
/// We reuse the untypified AST for this task.
/// The result of this analysis is a symbol table which contains a look-up
/// table. It allows to look up qualified names given a name and a range.
/// This is used in type checking to give identifiers unique names that
/// encode their scope.

[<RequireQualifiedAccess>]
module NameChecking = //TODO: @FJG: please clarify the notions "NameCheckContext", "SymbolTable", "Environment", "Lookup table"
                      //TODO: @FJG: please ensure their distinction from similar notions in subsequent phases
    open Blech.Common
    
    open CommonTypes
    open AST

    module Env = SymbolTable.Environment
    module Logger = Diagnostics.Logger

    type private TranslationUnitPath = TranslationUnitPath.TranslationUnitPath
    type private Environment = SymbolTable.Environment


    type NameCheckContext = 
        {
            env: Environment
            logger: Diagnostics.Logger
            importedLookupTables: Map<TranslationUnitPath, SymbolTable.LookupTable>
            importedExportScopes: Map<TranslationUnitPath, SymbolTable.Scope>
        }


    let initialise logger moduleName importedLookupTables importedExportScopes : NameCheckContext =
        { 
            env = Env.init moduleName
            logger = logger  // this will be create at blechc started and handed over
            importedLookupTables = importedLookupTables
            importedExportScopes = importedExportScopes
        }


    let private identifyNameInCurrentScope (ctx: NameCheckContext) (name: Name) =
        match Env.findNameInCurrentScope ctx.env name with
        | Ok env ->
            { ctx with env = env }
        | Error err -> 
            Logger.logError ctx.logger Diagnostics.Phase.Naming err
            ctx


    let private identifyStatic (ctx: NameCheckContext) (spath: AST.StaticNamedPath) =
        match Env.findCompletePath ctx.env spath with
        | Ok env ->            
            { ctx with env = env }
        | Error err ->
            Logger.logError ctx.logger Diagnostics.Phase.Naming err
            ctx


    let private identifyDynamic (ctx: NameCheckContext) (dpath: AST.DynamicAccessPath) =
        // let candidatePath = dpath.leadingNames
        match Env.findPartialPath ctx.env dpath with
        | Ok env ->
            { ctx with env = env }
        | Error err ->
            Logger.logError ctx.logger Diagnostics.Phase.Naming err
            ctx

    
    /// adds an imported module to the name check context
    let private addImportedModule (ctx: NameCheckContext) (import: AST.Import) = 
        let localName = import.localName
        let lookupTable = ctx.importedLookupTables.[import.modulePath.path]
        let exportScope = ctx.importedExportScopes.[import.modulePath.path]
        { ctx with env = Env.addImportedModule ctx.env localName lookupTable exportScope }


    let private addModuleNameDecl (ctx: NameCheckContext) (import: AST.Import) = 
        let name = import.localName
        match Env.insertModuleName ctx.env name with // check for shadowing
        | Ok env ->
            { ctx with env = env }
        | Error err ->
            Logger.logError ctx.logger Diagnostics.Phase.Naming err
            ctx
    
    let private addExposedImportedMember (import: AST.Import) (ctx: NameCheckContext) (exposedImportedMember: Name) =
        let modName = import.localName
        let modPath = import.modulePath
        match Env.exposeImportedMember ctx.env modName modPath exposedImportedMember with
        | Ok env ->
            { ctx with env = env }
        | Error err ->
            Logger.logError ctx.logger Diagnostics.Phase.Naming err
            ctx
     
    let private addDecl (ctx: NameCheckContext) (decl: AST.IDeclarable) (label: IdLabel) =
        let name = decl.name
        match Env.insertName ctx.env name label  with
        | Ok env ->
            { ctx with env = env }
        | Error err ->
            do Logger.logError ctx.logger Diagnostics.Phase.Naming err
            ctx     
        

    let private addConstOrParamDecl (ctx: NameCheckContext) (decl: AST.IDeclarable) =
        let name = decl.name
        match Env.insertConstOrParamName ctx.env name with
        | Ok env -> 
            { ctx with env = env }
        | Error err ->
            Logger.logError ctx.logger Diagnostics.Phase.Naming err
            ctx

    let private addUnitDecl = addConstOrParamDecl

    let private addTypeDecl (ctx: NameCheckContext) (sd: AST.IDeclarable) = 
        let name = sd.name
        match Env.insertTypeName ctx.env name with
        | Ok env ->
            { ctx with env = Env.enterOpenScope env name } // here is the difference to addDecl!
        | Error err ->
            Logger.logError ctx.logger Diagnostics.Phase.Naming err
            { ctx with env = Env.enterAnonymousScope ctx.env } // cannot be accessed because it is anonymous 
 
 
    let private addSubprogramDecl (ctx: NameCheckContext) name = 
        match Env.insertSubProgramName ctx.env name with  // wird im inner scope eingetragen
        | Ok env ->
            { ctx with env = Env.enterClosedScope env name }
        | Error err ->
            Logger.logError ctx.logger Diagnostics.Phase.Naming err
            { ctx with env = Env.enterAnonymousScope ctx.env }  // remains as anonymous inner scope

    let private addOpaqueSingletonDecl (ctx: NameCheckContext) name = 
        match Env.insertOpaqueSingletonName ctx.env name with  // wird im inner scope eingetragen
        | Ok env ->
            { ctx with env = env }
        | Error err ->
            Logger.logError ctx.logger Diagnostics.Phase.Naming err
            ctx 
            

    let private addSubScope (ctx: NameCheckContext) =
        { ctx with env = Env.enterAnonymousScope ctx.env }


    let private enableRecursion (ctx: NameCheckContext) =
        { ctx with env = Env.enableRecursiveCurrentScope ctx.env }


    let private exitSubScope (ctx: NameCheckContext) =
        { ctx with env = Env.exitInnerScope ctx.env }


    let private addExposedNameBefore (ctx: NameCheckContext) name =
        match Env.addExposedNameBefore ctx.env name with
        | Ok env ->
            { ctx with env = env }
        | Error err ->
            Logger.logError ctx.logger Diagnostics.Phase.Naming err       
            ctx

    let private addExposedNameAfter (ctx: NameCheckContext) name = 
        match Env.addExposedNameAfter ctx.env name with
        | Ok env ->
            { ctx with env = env }
        | Error err ->
            Logger.logError ctx.logger Diagnostics.Phase.Naming err       
            ctx

    let private addModuleScope (ctx: NameCheckContext) =
        { ctx with env = Env.enterModuleScope ctx.env }


    // begin ==========================================================
    // recursively descend the AST for name checking

    let rec checkUnitExpr ctx (ue: AST.UnitExpr) = 
        match ue with
        | UnitExpr.One _ ->
            ctx
        | UnitExpr.Parens (ue, _) ->
            checkUnitExpr ctx ue
        | UnitExpr.Unit sname ->
            identifyStatic ctx sname 
        | UnitExpr.UnitExp (ue, _, _) ->
            checkUnitExpr ctx ue
        | UnitExpr.UnitDiv (uel, uer)
        | UnitExpr.UnitMul (uel, uer) ->
            checkUnitExpr ctx uel 
            |> checkUnitExpr <| uer
 

    let checkLiteral ctx (lit: AST.Literal) = // checked because of units
        match lit with
        | Literal.Float (unit = ue)
        | Literal.Int (unit = ue) ->
            Option.fold checkUnitExpr ctx ue
        | _ ->
            ctx


    let rec checkCode ctx (c: AST.Code) =
        match c with
        | Code.Procedure fp   // will be dynamic with function pointers
            -> checkDynamicAccessPath ctx fp


    and checkStructField ctx field = 
        checkExpr ctx field.expr

    
    and checkArrayField ctx field =
        Option.fold checkExpr ctx field.index
        |> checkExpr <| field.value

    
    and checkAccess ctx (acc: AST.Access) =
        match acc with
        | Index (index = e)
        | StaticIndex (index = e) ->
            checkExpr ctx e
        | _ ->
            ctx    
    

    and checkDynamicAccessPath ctx (dPath: AST.DynamicAccessPath) =
        List.fold checkAccess ctx dPath.path
        |> identifyDynamic <| dPath


    and checkExpr ctx (exp: AST.Expr) =
        match exp with
            | Expr.Const lit ->
                checkLiteral ctx lit
            | Expr.AggregateConst (fieldExpr, _) ->
                match fieldExpr with
                | ResetFields -> ctx
                | StructFields fields -> List.fold checkStructField ctx fields
                | ArrayFields fields -> List.fold checkArrayField ctx fields
            | Expr.SliceConst _ ->
                ctx
            | Expr.Var pname ->
                checkDynamicAccessPath ctx pname
            | Expr.Not (e, _) 
            | Expr.Bnot (e, _)
            | Expr.Unm (e, _) 
            | Expr.Len (e, _)
            | Expr.Cap (e, _)
            | Expr.Parens (e, _) ->
                checkExpr ctx e
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
                |> checkExpr <| s1 
                |> checkExpr <| s2
            | Convert (expr, dty, _) 
            | HasType (expr, dty) ->
                ctx 
                |> checkExpr <| expr
                |> checkDataType <| dty
            | Expr.FunctionCall (fp, inputs, outputs, _) ->
                ctx
                |> checkCode <| fp
                |> List.fold checkExpr <| inputs
                |> List.fold checkDynamicAccessPath <| outputs


    and checkDataType ctx (dt: AST.DataType) =
        match dt with
        | BoolType _
        | BitvecType _ ->
            ctx
        | NaturalType (unit = uexp)
        | IntegerType (unit = uexp) 
        | FloatType (unit = uexp) ->
            Option.fold checkUnitExpr ctx uexp
        | ArrayType (size = expr; elem = dty) ->
            // resumeExposure ctx
            checkExpr ctx expr
            // |> disableExposure
            |> checkDataType <| dty
        | SliceType (elem = dty) ->
            checkDataType ctx dty
        | TypeName snp ->
            identifyStatic ctx snp
        | Signal (value = dt) ->
            Option.fold checkDataType ctx dt
  
  

    let checkParamDecl ctx (pd: AST.ParamDecl) = 
        List.fold identifyNameInCurrentScope ctx pd.sharing
        |> checkDataType <| pd.datatype
        |> addDecl <| pd <| IdLabel.Dynamic // added to scope last, not visible for sharing constraints and types


    let checkReturnDecl ctx (rd: AST.ReturnDecl) = 
        List.fold identifyNameInCurrentScope ctx rd.sharing
        |> checkDataType <| rd.datatype
 
 
    let checkVarDecl ctx (vd: AST.VarDecl) =
        let idLabel = if vd.permission.IsStatic then IdLabel.Static else IdLabel.Dynamic
        
        Option.fold checkDataType ctx vd.datatype
        |> Option.fold checkExpr <| vd.initialiser
        |> addDecl <| vd <| idLabel // added to scope last: 'const c: [1*c]int32 = 2*c' should be wrong


    let checkStaticVarDecl ctx (vd: AST.VarDecl) = 
        Option.fold checkDataType ctx vd.datatype
        |> Option.fold checkExpr <| vd.initialiser
        |> addConstOrParamDecl <| vd // added to scope last: 'const c: [1*c]int32 = 2*c' should be wrong


    let checkLocation ctx (lhs: AST.Receiver) =
        match lhs with
        | AST.Location (Loc l) -> 
            checkDynamicAccessPath ctx l
        | AST.FreshLocation vd ->
            Option.fold checkDataType ctx vd.datatype
            |> addDecl <| vd <| IdLabel.Dynamic 
        | _ ->
            ctx


    let checkCondition ctx (cond: AST.Condition) =
        match cond with
        | Condition.Cond e ->
            checkExpr ctx e
        | Condition.SignalBinding ob ->
            checkVarDecl ctx ob 
        | Condition.Tick (spath, _) ->
            identifyStatic ctx spath
  
  
    let rec checkStatement ctx (stmt: AST.Stmt) =
        match stmt with
        | LocalVar vdecl ->
            checkVarDecl ctx vdecl
            //Option.fold checkDataType ctx vdecl.datatype
            //|> Option.fold checkExpr <| vdecl.initialiser
            //|> addDecl <| vdecl

        | Assign (_, lhs, rhs) ->
            match lhs with
            | AST.Wildcard _ -> ctx
            | AST.Loc l -> checkDynamicAccessPath ctx l
            //| AST.FreshLoc _ -> failwith "This should never happen"
            |> checkExpr <| rhs

        | Assert (_, conds, msg) ->
            List.fold checkCondition ctx conds
            |> Option.fold checkExpr <| msg

        | Assume (_, conds, msg) ->
            List.fold checkCondition ctx conds
            |> Option.fold checkExpr <| msg

        | Await (_, conds) ->
            List.fold checkCondition ctx conds      // option bindings visible from here

        // TODO: Rather inelegant, can this be improved in the AST, fjg 02.08.2018 
        | ITE (_, conds, bodyIf, (bodyElse, isElseIf)) ->
            addSubScope ctx                         // scope starts at 'if' for option bindings
            |> List.fold checkCondition <| conds
            |> List.fold checkStatement <| bodyIf
            |> exitSubScope                         // scope closed at 'else'/'elseif'
            |> (fun ctx -> if isElseIf then ctx     // enter subscope in recursion for 'elseif'
                           else addSubScope ctx)    // scope starts for 'else', even when missing
            |> List.fold checkStatement <| bodyElse // [ITE] for 'elseif'
            |> (fun ctx -> if isElseIf then ctx     // exit subscope in recursion     
                           else exitSubScope ctx)   // scope closed at 'end' for 'else'

        | Cobegin (_, blockList) ->
            let chkBlock ctx (_, stmts) =           // ignore strength for name checking
                addSubScope ctx
                |> List.fold checkStatement <| stmts
                |> exitSubScope
            List.fold chkBlock ctx blockList

        | WhileRepeat (_, conds, body) ->
            addSubScope ctx                         // scope start at 'while' for option bindings
            |> List.fold checkCondition <| conds
            |> List.fold checkStatement <| body
            |> exitSubScope

        | RepeatUntil (_, body, conds) ->
            addSubScope ctx                         // scope starts at 'repeat'
            |> List.fold checkStatement <| body
            |> List.fold checkCondition <| conds    // options bindings only visible in 'until' conditions
            |> exitSubScope                         // scope closed at 'end'

        | NumericFor (_, var, init, limit, step, body) ->
            checkExpr ctx init
            |> checkExpr <| limit
            |> Option.fold checkExpr <| step
            |> addSubScope                          
            |> checkVarDecl <| var                  // loop var only visible inside loop
            |> List.fold checkStatement <| body 
            |> exitSubScope

        | IteratorFor (_, var, _, iterable, body) -> 
            checkExpr ctx iterable
            |> addSubScope                          
            |> checkVarDecl <| var                  // loop var only visible inside loop
            |> List.fold checkStatement <| body 
            |> exitSubScope

        | Preempt (_, _, conds, _, body) ->            
            List.fold checkCondition ctx conds      // option bindings not visible inside body
            |> addSubScope                          
            |> List.fold checkStatement <| body
            |> exitSubScope

        | Stmt.SubScope (_, body) ->
            addSubScope ctx                         // scope starts at 'do'
            |> List.fold checkStatement <| body
            |> exitSubScope                         // scope closed at 'end'

        | ActivityCall (_, optReceiver, ap, inputs, outputs) -> 
            // fresh location added to scope last, 'run let x = Activity(x)' should be wrong
            checkCode ctx ap
            |> List.fold checkExpr <| inputs
            |> List.fold checkDynamicAccessPath <| outputs
            |> Option.fold checkLocation <| optReceiver 

        | FunctionCall (_, fp, inputs, outputs) ->
            checkCode ctx fp
            |> List.fold checkExpr <| inputs
            |> List.fold checkDynamicAccessPath <| outputs

        | Emit (_, receiver, optExpr) ->
            // fresh location added to scope last, 'emit let x = x + 1' should be wrong
            Option.fold checkExpr ctx optExpr 
            |> checkLocation <| receiver

        | Return (_, expr) ->
            Option.fold checkExpr ctx expr 
            
        | Pragma _ 
        | Nothing ->
            ctx
 
 
    let checkSubprogram ctx (sp: AST.SubProgram) =
        addSubprogramDecl ctx sp.name
        |> List.fold identifyStatic <| sp.singletons
        |> List.fold checkParamDecl <| sp.inputs
        |> List.fold checkParamDecl <| sp.outputs
        |> Option.fold checkReturnDecl <| sp.result
        |> List.fold checkStatement <| sp.body
        |> exitSubScope
        // |> exportCodeDecl <| sp.name


    let checkFunctionPrototype ctx (fp: AST.Prototype) =
        addSubprogramDecl ctx fp.name
        |> List.fold identifyStatic <| fp.singletons
        |> List.fold checkParamDecl <| fp.inputs
        |> List.fold checkParamDecl <| fp.outputs
        |> Option.fold checkReturnDecl <| fp.result
        |> exitSubScope
        

    let checkOpaqueSingleton ctx (os: AST.OpaqueSingleton) =
        List.fold identifyStatic ctx os.singletons
        |> addOpaqueSingletonDecl <| os.name
        

    let checkUnitDecl ctx (ud: AST.UnitDecl) =
        addUnitDecl ctx ud
 
 
    let checkTagDecl ctx (td: AST.TagDecl) =
        Option.fold checkExpr ctx td.rawvalue
        |> addDecl <| td <| IdLabel.Static
        

    // all field names are syntactically var decls
    let checkFieldDecl ctx (field: AST.Member) =
        match field with
        | Member.Var fdecl ->    
            Option.fold checkDataType ctx fdecl.datatype
            |> Option.fold checkExpr <| fdecl.initialiser
            |> addDecl <| fdecl <| IdLabel.Static
        | _ -> // other members do no occur as fields
            ctx


    let checkImportExposes import ctx (exposing: AST.Exposing) =
        List.fold (addExposedImportedMember import) ctx exposing.names
        

    let checkImport ctx (import: AST.Import) = 
        addModuleNameDecl ctx import
        |> addImportedModule <| import
        |> Option.fold (checkImportExposes import) <| import.exposing


    let rec checkEnumType ctx (etd: AST.EnumTypeDecl) =
            addTypeDecl ctx etd                           // open, named, non-recursive
            |> Option.fold checkDataType <| etd.rawtype   // check rawtype first 
            |> enableRecursion                            
            |> List.fold checkTagDecl <| etd.tags
            |> List.fold checkMember <| etd.members
            |> exitSubScope
            

        and checkStructType ctx (std: AST.StructTypeDecl) =
            addTypeDecl ctx std                        // add non-recursive sub scope
            |> addSubScope                             // separate anonymous scope for fields, prevents open access
            |> List.fold checkFieldDecl <| std.fields  // check fields first, before typename becomes visible  
            |> exitSubScope      
            |> enableRecursion                         
            |> List.fold checkMember <| std.members
            |> exitSubScope
            

        and checkOpaqueType ctx (ntd: AST.OpaqueTypeDecl) =
            addTypeDecl ctx ntd                 // open, named, non-recursive scope 
            |> enableRecursion                         
            |> List.fold checkMember <| ntd.members
            |> exitSubScope
            

        and checkTypeAlias ctx (tad: AST.TypeAliasDecl) =
            addTypeDecl ctx tad                 // open, named, non-recursive scope
            |> checkDataType <| tad.aliasfor          // check alias first, before typename becomes visible
            |> enableRecursion
            |> List.fold checkMember <| tad.members
            |> exitSubScope
            

        and checkMember ctx (m: AST.Member) =
            match m with
            | Member.EnumType et ->
                checkEnumType ctx et
            | Member.StructType st ->
                checkStructType ctx st
            | Member.OpaqueType nt ->
                checkOpaqueType ctx nt
            | Member.TypeAlias ta -> 
                checkTypeAlias ctx ta
            | Member.Var vdecl ->
                checkStaticVarDecl ctx vdecl
            | Member.Subprogram sp ->
                checkSubprogram ctx sp
            | Member.Prototype fp ->
                checkFunctionPrototype ctx fp
            | Member.OpaqueSingleton os ->
                checkOpaqueSingleton ctx os
            | Member.Unit u ->
                checkUnitDecl ctx u
            | Member.Clock _ ->
                ctx //TODO
            | Member.Pragma _->
                ctx 
            | Member.Nothing -> 
                ctx

    
    let checkExposingBefore ctx (exposing: AST.Exposing) =
        List.fold addExposedNameBefore ctx exposing.names
        

    let checkModuleSpecBefore ctx (modSpec: AST.ModuleSpec) =
        Option.fold checkExposingBefore ctx modSpec.exposing


    let checkExposingAfter (ctx: NameCheckContext) (exposing: AST.Exposing) = 
        List.fold addExposedNameAfter ctx exposing.names 
        

    let checkModuleSpecAfter (ctx: NameCheckContext) (modSpec: AST.ModuleSpec) : NameCheckContext = 
        Option.fold checkExposingAfter ctx modSpec.exposing


    let checkCompilationUnit (ctx: NameCheckContext) (cu: AST.CompilationUnit) : NameCheckContext =
        // printfn "Namecheck Compilation Unit: %s" <| string cu.moduleName
        // this should create an intermediate scope after the imports, lets call it module scope
        List.fold checkImport ctx cu.imports
        |> addModuleScope  // all compilation units get a module scope
        |> Option.fold checkModuleSpecBefore <| cu.moduleSpec
        |> List.fold checkMember <| cu.members
        |> Option.fold checkModuleSpecAfter <| cu.moduleSpec     // check exposes <identifiers> last 
    
    
    // TODO: Maybe we should define different entry points, for (incremental) parsing and checking
    let checkDeclaredness (ctx: NameCheckContext) (ast: AST.CompilationUnit) = 
        let ncc = checkCompilationUnit ctx ast
        if Diagnostics.Logger.hasErrors ncc.logger then
            Error ncc.logger
        else
            Ok ncc.env
    

    // end ============================================================
