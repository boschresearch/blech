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

/// This module contains all functionality which is specific for the
/// translation of Blech functions to C code.
[<RequireQualifiedAccess>]
module Blech.Backend.FunctionTranslator

open System.Collections.Generic

open Blech.Common.PPrint.PPrint

open Blech.Frontend
open Blech.Frontend.CommonTypes
open Blech.Frontend.BlechTypes
open Blech.Frontend.PrettyPrint.DocPrint
open Blech.Frontend.TyChkExpressions

open Blech.Backend

open Normalisation
open CPdataAccess
open CPrinter


let rec private translateFunctionStatements ctx curComp stmts =
    stmts
    |> List.map (translateFunctionStatement ctx curComp)
    |> dpBlock
and private translateFunctionStatement ctx curComp stmt =
    match stmt with
    | Stmt.VarDecl v ->
        // If this declares a constant, do not generate any code here. The
        // declaration will appear on the top level.
        if v.IsConst then
            txt "/* The local const declaration was lifted to top level */"
        elif v.IsParam then
            txt "/* The local param declaration was lifted to top level */"
        else
            // Otherwise (let, var)
            // add v to local variables. Unlike activities in functions we do not expose local
            // variables in the interface but nonetheless they are needed to distinguish between
            // local and output variable access which for primitive types is direct or derefenrecing.
            let newIface = Iface.addLocals (!curComp).iface {pos = v.pos; name = v.name; datatype = v.datatype; isMutable = v.mutability.Equals Mutability.Variable; allReferences = HashSet()}
            curComp := {!curComp with iface = newIface}
            let norm =
                normaliseVarDecl ctx.tcc v
                |> List.map (function 
                    | Stmt.Assign(_, lhs, rhs) -> 
                        match lhs.typ with
                        | ValueTypes (ArrayType _) ->
                            cpMemCpyArr true ctx lhs.lhs rhs
                        | _ ->
                            cpAssignInFunction ctx lhs.lhs rhs
                    | _ -> failwith "Must be an assignment here!") // not nice
            match v.datatype with
            | ValueTypes (ValueTypes.StructType _) 
            | ValueTypes (ValueTypes.ArrayType _) ->
                let init = cpArrayDecl v.name v.datatype <^> semi
                // re-initialise the whole blob and then set the given fields
                let reinit = cpMemSet true ctx {lhs = LhsCur(Loc v.name); typ = v.datatype; range = v.pos}
                init :: reinit :: norm |> vsep
            | _ ->
                let prereqStmt, processedRhs = cpExprInFunction ctx v.initValue
                let init = cpArrayDecl v.name v.datatype <+> txt "=" <+> processedRhs <^> semi
                prereqStmt @ [init] |> vsep
                
    // actions
    | Stmt.Assign (r, lhs, rhs) ->
        let norm =
            normaliseAssign ctx.tcc (r, lhs, rhs)
            |> List.map (function 
                | Stmt.Assign(_, lhs, rhs) -> 
                    match lhs.typ with
                    | ValueTypes (ArrayType _) ->
                        cpMemCpyArr true ctx lhs.lhs rhs
                    | _ ->
                        cpAssignInFunction ctx lhs.lhs rhs
                | _ -> failwith "Must be an assignment here!") // not nice
        match rhs.rhs with
        | StructConst _
        | ArrayConst _ when isLiteral rhs->
            // re-initialise the whole blob and then set the given fields
            let reinit = cpMemSet true ctx lhs
            reinit :: norm |> vsep
        | _ ->
            let prereqStmts, transExpr = makeTmpForComplexConst true ctx rhs 
            match transExpr with
            | Orig _ ->
                match lhs.typ with
                | ValueTypes (ArrayType _) -> // a = b; where a, b are arrays
                    cpMemCpyArr true ctx lhs.lhs rhs
                | _ ->
                    cpAssignInFunction ctx lhs.lhs rhs
            | Done d ->
                let cpy = cpMemCpyDoc true ctx lhs d
                prereqStmts @ [cpy] |> vsep
    | Stmt.Assert _
    | Stmt.Assume _
    | Stmt.Print _ -> failwith "Print, Assert, Assume not implemented yet."
    // control flow
    | ITE (_, cond, ifBranch, elseBranch) -> // line, condition, if-block, else-block (each possibly empty!)
        let prereqStmts, transCond = cpExprInFunction ctx cond
        let transIfBranch = translateFunctionStatements ctx curComp ifBranch
        let ifStmt =
            if elseBranch = [] then 
                cpIfOnly transCond transIfBranch
            else
                let transElseBranch = translateFunctionStatements ctx curComp elseBranch
                cpIfElse transCond transIfBranch transElseBranch
        prereqStmts @ [ifStmt]
        |> dpBlock
    | WhileRepeat (_, cond, body) ->
        let prereqStmts, transCond = cpExprInFunction ctx cond
        let transBody = translateFunctionStatements ctx curComp body
        prereqStmts @ [ cpWhile transCond transBody ]
        |> dpBlock
    | RepeatUntil (_, body, cond, false) ->
        let negatedCond = { rhs = unsafeNeg cond
                            typ = cond.typ
                            range = cond.range }
        let prereqStmts, transCond = cpExprInFunction ctx negatedCond
        let transBody = translateFunctionStatements ctx curComp body
        prereqStmts @ [ cpRepeatUntil transCond transBody ]
        |> dpBlock
    // scoping
    | StmtSequence stmts -> translateFunctionStatements ctx curComp stmts
    // calling
    | Stmt.FunctionCall (pos, whoToCall, inputs, outputs) ->
        // Since function calls statements and expressions are translated in the same way
        // simply call the expression translation here
        let prereqStmts, processedCall =
            {rhs = FunCall (whoToCall, inputs, outputs); typ = Types.ValueTypes Void; range = pos}
            |> cpExprInFunction ctx
        prereqStmts @ [ processedCall <^> semi ]
        |> dpBlock
    | Stmt.Return (r, exprOpt) ->
        // in order to use functions in expression they directly have to return the value without using a retvar
        // the programmer has to introduce such a helper variable himself if he needs to return complex value type structures
        match exprOpt with
        | None -> txt "return;" // in contrast to activities we actually do a void return to terminate execution
        | Some expr ->
            if expr.typ.IsPrimitive then // if primitive simply "return expr;"
                let prereqStmts, processedExpr = cpExprInFunction ctx expr
                prereqStmts @ [
                    txt "return" <+> processedExpr <^> semi
                    ]
                |> dpBlock
            else // otherwise copy the value into retvar
                // construct typed lhs
                let lhs =
                    let name = (!curComp).iface.retvar |> Option.get |> (fun p -> p.name)
                    let typ =
                        match ctx.tcc.nameToDecl.[(!curComp).name] with
                        | FunctionPrototype p -> p.returns
                        | SubProgramDecl d -> d.returns
                        | _ -> failwith "expected subprogram, got something else"
                    { lhs = LhsCur (Loc name)
                      typ = ValueTypes typ
                      range = r }
                // call this function recursively with an Assign action and make a void return
                [ translateFunctionStatement ctx curComp (Stmt.Assign(r, lhs, expr))
                  txt "return;" ]
                |> dpBlock

    // synchronous statements
    | Await _ 
    | Cobegin _ 
    | RepeatUntil (_,_,_,true)
    | Preempt _ 
    | ActivityCall _ -> failwith "Synchronous control flow in a function should have been ruled out by the type checker."

// Statements of functions cannot be interleaved with other concurrent statements.
// Hence we can generate a program coutner free code, disregarding the individual blocks.
/// Returns the translated function body
let private translateFunction ctx curComp (funDecl: SubProgramDecl) =
    assert funDecl.isFunction
    funDecl.body
    |> translateFunctionStatements ctx curComp

let internal translate ctx (subProgDecl: SubProgramDecl) =
    let name = subProgDecl.name
    
    let retvar, retType =
        if subProgDecl.returns.IsPrimitive then
            None, cpType (Types.ValueTypes subProgDecl.returns)
        else
            let qname = QName.Create subProgDecl.name.moduleName (subProgDecl.name.prefix @ [subProgDecl.name.basicId]) "retvar" Dynamic
            let v = { name = qname
                      pos = subProgDecl.pos
                      datatype = Types.ValueTypes subProgDecl.returns
                      isMutable = true 
                      allReferences = HashSet() }
            ctx.tcc.nameToDecl.Add(qname, Declarable.ParamDecl v)
            Some v, cpType (ValueTypes Void)
    
    let iface = {Iface.Empty with inputs = subProgDecl.inputs; outputs = subProgDecl.outputs; retvar = retvar}
    
    let curComp = ref {Compilation.Empty with name = name; iface = iface}
    
    let code = translateFunction ctx curComp subProgDecl
    
    let completeFunctionCode =
        txt "static" // TODO must be non-static if function is exposed, fjg 17.01.19
        <+> retType
        <+> ppName (!curComp).name
        <+> cpFunctionIface (!curComp).iface
        <+> txt "{"
        <.> cpIndent code
        <.> txt "}"

    let signature =
        retType
        <+> ppName (!curComp).name
        <+> cpFunctionIface (!curComp).iface
        <^> semi

    let optDoc = 
        cpOptDocComments subProgDecl.annotation.doc

    curComp := { !curComp with 
                    signature = signature
                    implementation = completeFunctionCode 
                    doc = optDoc }
    !curComp