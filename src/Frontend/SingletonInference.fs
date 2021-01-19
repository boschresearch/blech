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


module SingletonInference = 

    open Blech.Common
    open CommonTypes
    open AST

    
     
    //type SingletonSignature = 
    //    | Opaque of LongIdentifier list       // e.g. singleton [f, g] h
    //    | Translucent of LongIdentifier list  // e.g. singleton [f, g] function h ()
    
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

    module Env = SymbolTable.Environment
        
    type private SingletonUse = Name list 
    type Singletons = Map<Name, SingletonUse list> // declaration name |-> singleton calls (multiple occurences of the same singleton possible)

    type SingletonContext = 
        private {
            logger : Diagnostics.Logger
            environment : SymbolTable.Environment
            calledSingletons : SingletonUse list // accumulator for singleton calls, in reverse order of appearance
            singletons : Singletons
        }

        static member Initialise (logger: Diagnostics.Logger) 
                                 (env: SymbolTable.Environment) 
                                 (importedSingletons: Singletons list) = 
            {   
                logger = logger
                environment = env
                
                calledSingletons = List.Empty
                singletons = Map.collectWithOverride importedSingletons // might contain duplicates
            }
            // |> fun ctx -> printfn "##########\nInitialised singletons: %A\n################" ctx.singletons; ctx

        member this.CollectSingletons declName : QName list = 
            let env = this.environment
            let rec recurse path =
                let lastname = List.last path
                let declname = Env.getDeclName env lastname
                let qname = (Env.getLookupTable env).nameToQname declname
                match this.singletons.Item declname with
                | [] -> [qname]
                | singletons -> 
                    qname :: List.collect recurse singletons

            List.collect recurse (this.singletons.Item declName)
            |> List.distinct
        
        member this.IsSingleton name = 
            if Env.isStaticName this.environment name then 
                let declName = Env.getDeclName this.environment name
                //printfn "???????\n IsSingleton name: %A\n decl name: %A\n??????????" name declName
                this.singletons.ContainsKey declName
            else
                false

        //member this.HasOpaqueSingletonSignature name = 
        //    let declName = Env.getDeclName this.environment name
        //    match this.singletons.signatures.TryFind declName with
        //    | Some (Opaque _) -> true
        //    | _ -> false
          
        //member this.TryGetSingletonSignature name = 
        //    let declName = Env.getDeclName this.environment name
        //    this.singletons.signatures.TryFind declName
              
        member this.HasCalledSingletons = 
            not <| List.isEmpty this.calledSingletons

        member this.AddSingleton declName =
            assert Env.isDeclName this.environment declName
            { this with 
                singletons = Map.add declName this.calledSingletons this.singletons 
                calledSingletons = List.empty }

        //member this.GetSingletons = 
        //    this.singletons
            

    type SingletonError = 
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

    let private logSingletonError ctx err  = 
        do Diagnostics.Logger.logError ctx.logger Diagnostics.Phase.Singletons err
        ctx
        
    // begin ==========================================
    // recursively descend the AST for export inference

    let private addToSingletons isDeclaredSingleton (ctx: SingletonContext) (name: Name) : SingletonContext =
        if isDeclaredSingleton || ctx.HasCalledSingletons then
            // printfn "Add singleton: %s" name.id
            ctx.AddSingleton name
        else
            ctx


    let private addSingletonUsageDeclaration (ctx : SingletonContext) (snp : AST.StaticNamedPath) = 
        let lastName = List.last snp.names
        if not <| ctx.IsSingleton lastName then 
            Dummy (snp.Range, sprintf "Declared singleton usage '.%s' is not a singleton" snp.dottedPathToString )
            |> logSingletonError ctx 
        else
            { ctx with calledSingletons = snp.names :: ctx.calledSingletons }
      
    let private addSingletonCall (ctx : SingletonContext) (dap : AST.DynamicAccessPath) =
        let leadingNames = dap.leadingNames
        let lastName = List.last dap.leadingNames
        if ctx.IsSingleton lastName then 
            { ctx with calledSingletons = leadingNames :: ctx.calledSingletons }
        else
            ctx

    let private inferStaticNamedPath = 
        addSingletonUsageDeclaration

    let private inferDynamicNamePath =
        addSingletonCall
        
    // TODO: Currently a function call is not possible for an implicit member
    // implicit members should be usable for all static and dynamic access paths
    let private inferImplicitMember ctx (snp : AST.StaticNamedPath) =  
        ctx
    
    // TODO: Singletons should not be usable as function references, i.e. they become 2nd class subprograms
    let private inferNameInCurrentScope ctx (sharing: Name) = 
        ctx
    
    //let rec private inferUnitExpr ctx (ue: AST.UnitExpr) = 
    //    match ue with
    //    | UnitExpr.One _ ->
    //        ctx
    //    | UnitExpr.Parens (ue, _) ->
    //        inferUnitExpr ctx ue
    //    | UnitExpr.Unit sname ->
    //        inferStaticNamedPath ctx sname 
    //    | UnitExpr.UnitExp (ue, _, _) ->
    //        inferUnitExpr ctx ue
    //    | UnitExpr.UnitDiv (uel, uer)
    //    | UnitExpr.UnitMul (uel, uer) ->
    //        inferUnitExpr ctx uel 
    //        |> inferUnitExpr <| uer
 
    
    //let private inferLiteral ctx (lit: AST.Literal) = // infered because of units
    //    match lit with
    //    | Literal.Float (unit = ue)
    //    | Literal.Int (unit = ue) ->
    //        Option.fold inferUnitExpr ctx ue
    //    | _ ->
    //        ctx

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

    and private inferExpr ctx (expr: AST.Expr) =
        match expr with
        | Expr.Const lit ->
            ctx
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
            // |> inferDataType<| dty
        | Expr.FunctionCall (fp, inputs, outputs, _) ->
            ctx
            |> inferCode <| fp
            |> List.fold inferExpr <| inputs
            |> List.fold inferDynamicAccessPath <| outputs

 
    //and private inferDataType ctx (dt: AST.DataType) =
    //    match dt with
    //    | BoolType _
    //    | BitvecType _
    //    | NaturalType _
    //    | IntegerType _ 
    //    | FloatType _
    //    | TypeName _ ->
    //        ctx
    //    | ArrayType (size = expr; elem = dty) ->
    //        inferExpr ctx expr
    //        |> inferDataType <| dty
    //    | SliceType (elem = dty) ->
    //        inferDataType ctx dty
    //    | Signal (value = dt) ->
    //        Option.fold inferDataType ctx dt
  
  

    //let private inferParamDecl ctx (pd: AST.ParamDecl) = 
    //    List.fold inferNameInCurrentScope ctx pd.sharing
    //    |> inferDataType <| pd.datatype


    //let private inferReturnDecl ctx (rd: AST.ReturnDecl) = 
    //    List.fold inferNameInCurrentScope ctx rd.sharing
    //    |> inferDataType <| rd.datatype
 
 
    let private inferVarDecl ctx (vd: AST.VarDecl) =
        // Option.fold inferDataType ctx vd.datatype
        Option.fold inferExpr ctx vd.initialiser


    //let private inferStaticVarDecl ctx (vd: AST.VarDecl) =
    //    Option.fold inferDataType ctx vd.datatype
    //    |> Option.fold inferExpr <| vd.initialiser
        

    //let private inferLocation ctx (lhs: AST.Receiver) =
    //    match lhs with
    //    | AST.FreshLocation vd ->
    //        Option.fold inferDataType ctx vd.datatype
    //    | AST.Location _
    //    | AST.ReturnLocation _ ->
    //        ctx


    // TODO: Conditions must not have side effects and therefore must not call singletons - check this in type checking
    let private inferCondition ctx (cond: AST.Condition) =
        match cond with
        | Condition.Cond e ->
            inferExpr ctx e
        | Condition.SignalBinding ob ->
            inferVarDecl ctx ob 
        | Condition.Tick _ ->
            ctx
            // inferStaticNamedPath ctx spath
  
  
    let rec private inferStatement ctx (stmt: AST.Stmt) =
        match stmt with
        | LocalVar vdecl ->
            inferVarDecl ctx vdecl

        | Assign (_, lhs, rhs) ->
            inferExpr ctx rhs

        | Assert (_, conds, msg) ->
            List.fold inferCondition ctx conds
            |> Option.fold inferExpr <| msg

        | Assume (_, conds, msg) ->
            List.fold inferCondition ctx conds
            |> Option.fold inferExpr <| msg

        | Await (_, conds) ->
            List.fold inferCondition ctx conds

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
            |> List.fold inferCondition <| conds

        | NumericFor (_, var, init, limit, step, body) ->
            inferExpr ctx init
            |> inferExpr <| limit
            |> Option.fold inferExpr <| step
            |> inferVarDecl <| var
            |> List.fold inferStatement <| body 

        | IteratorFor (_, var, _, iterable, body) -> 
            inferExpr ctx iterable
            |> inferVarDecl <| var
            |> List.fold inferStatement <| body 

        | Preempt (_, _, conds, _, body) ->            
            List.fold inferCondition ctx conds
            |> List.fold inferStatement <| body

        | Stmt.SubScope (_, body) ->
            List.fold inferStatement ctx body

        | ActivityCall (_, optReceiver, ap, inputs, outputs) -> 
            inferCode ctx ap
            |> List.fold inferExpr <| inputs
            |> List.fold inferDynamicAccessPath <| outputs
            // |> Option.fold inferLocation <| optReceiver 

        | FunctionCall (_, fp, inputs, outputs) ->
            inferCode ctx fp
            |> List.fold inferExpr <| inputs
            |> List.fold inferDynamicAccessPath <| outputs

        | Emit (_, receiver, optExpr) ->
            Option.fold inferExpr ctx optExpr 
            //|> inferLocation <| receiver

        | Return (_, expr) ->
            Option.fold inferExpr ctx expr 
        
        | Pragma _ 
        | Nothing ->
            ctx
 
 
    let private inferSubprogram ctx (sp: AST.SubProgram) =
        List.fold inferStaticNamedPath ctx sp.singletons
        |> List.fold inferStatement <| sp.body
        |> (addToSingletons sp.isSingleton) <| sp.name


    let private inferFunctionPrototype ctx (fp: AST.Prototype) =
        List.fold inferStaticNamedPath ctx fp.singletons
        |> (addToSingletons fp.isSingleton) <| fp.name


    let private inferOpaqueSingleton ctx (os: AST.OpaqueSingleton) =
        List.fold inferStaticNamedPath ctx os.singletons
        |> (addToSingletons true) <| os.name


    //let private inferUnitDecl ctx (ud: AST.UnitDecl) =
    //    ctx

    //let private inferTagDecl ctx (td: AST.TagDecl) =
    //    Option.fold inferExpr ctx td.rawvalue
        

    // all field names are syntactically var decls
    //let private inferFieldDecl ctx (field: AST.Member) =
    //    match field with
    //    | Member.Var fdecl ->  
    //        Option.fold inferDataType ctx fdecl.datatype
    //        |> Option.fold inferExpr <| fdecl.initialiser
    //    | _ -> // other members do no occur as fields
    //        ctx

    let rec private inferEnumType ctx (etd: AST.EnumTypeDecl) =
        //Option.fold inferDataType ctx etd.rawtype    
        //|> List.fold inferTagDecl <| etd.tags  // raw values must be checked
        List.fold inferExtensionMember ctx etd.members
        

    and private inferStructType ctx (std: AST.StructTypeDecl) =
        // List.fold inferFieldDecl ctx std.fields  // infer fields because of initialisers  
        List.fold inferExtensionMember ctx std.members
        

    and private inferOpaqueType ctx (ntd: AST.OpaqueTypeDecl) =
        List.fold inferExtensionMember ctx ntd.members
        

    and private inferTypeAlias (ctx: SingletonContext) (tad: AST.TypeAliasDecl) =
        // inferDataType ctx tad.aliasfor
        List.fold inferExtensionMember ctx tad.members  // TODO: change this to something like inferMethod
        

    // TODO: Rethink extension subprogram members
    and private inferExtensionMember ctx (em: AST.Member) = 
        match em with
        | Member.TypeAlias ta ->
            inferTypeAlias ctx ta
        | Member.Var svd ->
            // inferStaticVarDecl ctx svd
            ctx
        | Member.Subprogram sp -> 
            inferSubprogram ctx sp
        | Member.Prototype fp ->
            inferFunctionPrototype ctx fp
        | _ ->
            failwith "îllegal member in extension, this should have been excluded by the parser"


    let private inferTopLevelMember (ctx: SingletonContext) (m: AST.Member) =
        match m with
        | Member.EnumType et ->
            inferEnumType ctx et
        | Member.StructType st ->
            inferStructType ctx st
        | Member.OpaqueType ot ->
            inferOpaqueType ctx ot
        | Member.TypeAlias ta ->
            inferTypeAlias ctx ta
        | Member.Var svd ->
            ctx
            // inferStaticVarDecl ctx svd
        | Member.Subprogram sp ->
            inferSubprogram ctx sp
        | Member.Prototype fp ->
            inferFunctionPrototype ctx fp
        | Member.OpaqueSingleton os ->
            inferOpaqueSingleton ctx os
        | Member.Unit u ->
            ctx
            // inferUnitDecl ctx u
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

    //let private inferImport (ctx: SingletonContext) (import: AST.Import) = 
    //    Option.fold inferImportExposing ctx import.exposing


    // ModuleSpec 
    //let private inferExposing ctx (exposing: AST.Exposing) = 
    //    ctx 
        

    //let private inferModuleSpecLast ctx (modSpec: AST.ModuleSpec) = 
    //    Option.fold inferExposing ctx modSpec.exposing

    //let addExposedImportedSingleton (ctx : SingletonContext) name =
    //    let declName 
    //    ctx

    
    // Compilation Unit
    let private inferCompilationUnit (ctx: SingletonContext) (cu: AST.CompilationUnit) =
        List.fold inferTopLevelMember ctx cu.members
        
    // end =========================================
    
    
    let inferSingletons logger (env: SymbolTable.Environment) 
                               (importedSingletons : Singletons list)
                               (cu: AST.CompilationUnit) =
        let ctx =
            SingletonContext.Initialise logger env importedSingletons
            |> inferCompilationUnit <| cu
        // just for debugging
        // printfn "Singletons: \n %A" ctx.singletons
        if Diagnostics.Logger.hasErrors ctx.logger then
            Error ctx.logger
        else
            Ok ctx.singletons

