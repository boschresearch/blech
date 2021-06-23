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

namespace Blech.Intermediate

open Blech.Frontend.Constants
open Blech.Frontend.BlechTypes


module GenericGraph = Blech.Common.GenericGraph
module Range = Blech.Common.Range


/// Contains helper functions for other modules in this file.
/// These functions manage the creation of distinct IDs.
module Utils =
    // this is used to generate unique IDs for threads
    let mutable private _counter = 0
    let getFreshThreadId () =
        _counter <- _counter + 1
        _counter


/// This module combines all functions related to threads.
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Thread =

    let private _createThread parent fork =
        { ID = Utils.getFreshThreadId()
          Ancestor = parent
          Fork = fork }

    /// Returns a record of type Thread with a distinct ID
    /// and no ancestor and no fork.
    let internal newThread () = _createThread None None
        
    /// Returns a record of type Thread with a distict ID
    /// and sets the given parent thread and fork location.
    let internal newChildThread parent fork = _createThread (Some parent) (Some fork)

    /// Returns all ancestors starting with this thread itself and
    /// ascending to root
    let rec allAncestors thread =
        match thread.Ancestor with
        | None -> [thread]
        | Some ancestor -> thread :: allAncestors ancestor

    /// Returns a list of fork nodes starting with the node where this
    /// thread has been forked off (in the parent thread) and ascending
    /// to the node in the root thread that forked off this control
    /// flow branch.
    /// The list is empty in case thread is the root!
    let rec internal allForks thread =
        match thread.Fork with
        | None -> []
        | Some fork ->
            match thread.Ancestor with
            | None -> [fork] // this will never happen, if thread was forked, then there is an ancestor who contains that fork node
            | Some ancestor -> fork :: allForks ancestor

    let internal strictlyContains parent child =
        let allAncestorsWithoutSelf = 
            allAncestors child
            |> List.filter (fun t -> not (t = child))
        List.contains parent allAncestorsWithoutSelf
        
    // Two threads are concurrent when neither is the ancestor of the other.
    // This includes the fact that they must be distinct.
    // And they must be forked off a common ancestor at the same fork node.
    let internal areConcurrent thread1 thread2 =
        let neitherIsAncestor = (not (List.contains thread1 (allAncestors thread2))) && (not (List.contains thread2 (allAncestors thread1)))
        // find least common ancestor thread (always exists, root in the worst case)
        let lcaOpt = allAncestors thread1 |> List.tryFind (fun t -> List.contains t (allAncestors thread2)) // relies on the fact that ancestors are sorted
        match lcaOpt with
        | None -> failwith "Two threads must have at least the root in common! Something is horribly wrong here! STAAHP!!"
        | Some lca -> 
            // find least common fork (may not exist if root is the lca)
            let lcfOpt = allForks thread1 |> List.tryFind (fun f -> List.contains f (allForks thread2))
            match lcfOpt with
            | None -> false
            | Some lcf ->
                // concurrent if neither is ancestor of the other and lcf exists and lies in lca
                neitherIsAncestor && lcf.Payload.Thread = lca


/// Module with functionality for managing the intermediate context
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module IntermediateContext =
    open Blech.Frontend

    /// Given a typed memory location, get all its subelements, if any
    // add type check lut to context
    // for any tml, look up its type
    // if type is struct then return
    //    for every field allMemLocs FieldAccess(tml, field)
    // else return [tml]
    let rec private allMemLocs context (tml: TypedMemLoc) =
        match tml.GetPrefixBeforeArrayAccess with
        | Some t -> [ t ]
        | None ->
            match TypeCheckContext.getDatatypeFromTML context.lut tml with
            | ValueTypes (ValueTypes.StructType (_, fields))
            | ReferenceTypes (ReferenceTypes.StructType (_, _, fields)) ->
                [
                    for field in fields do
                        yield! allMemLocs context (tml.AddFieldAccess field.name.basicId)
                ]
            | _ -> [ tml ]

    let private appendValue (dictionary: Mem2Nodes) r n key =
        if not (dictionary.ContainsKey(key)) then
            do dictionary.Add(key, ResizeArray())
        do dictionary.[key].Add(r,n)

    let private appendToCtx mem2NodesDict context pos memLab node =
        memLab 
        |> MemoryLabel.mapLst (allMemLocs context)
        |> List.iter (appendValue mem2NodesDict pos node)
    
    let private appendAllWritten context =
        appendToCtx context.tempNameWrittenByNodes context
        
    let private appendAllRead context =
        appendToCtx context.tempNameReadByNodes context

    let private addSingletonCall context range node name =
        appendValue context.tempNameWrittenByNodes range node (SubProg name)

    let internal addSingletonCalls context range node whoToCall =
        // look up what whoToCall is (SubProgramDecl / FunctionPrototype)
        // and determine the list of singletons downstream
        let names =
            match context.lut.nameToDecl.[whoToCall] with
            | ProcedureImpl s -> s.Singletons
            | ProcedurePrototype p -> p.singletons
            | Declarable.VarDecl _ 
            | Declarable.ExternalVarDecl _ 
            | Declarable.ParamDecl _ -> failwith "Expected whoToCall to be a a function or activity or prototype declaration."
        // add each one to given node
        List.iter (addSingletonCall context range node) names

    let rec internal addNameWritten context node (tlhs: TypedLhs) =
        let addWrittenLabel memLabel =
            do appendAllWritten context tlhs.Range memLabel node
        match tlhs.lhs with
        | Wildcard -> ()
        | ReturnVar -> ()
        | LhsCur tml ->
            tml.FindAllIndexExpr |> Seq.iter (addNameRead context node)
            do addWrittenLabel (AccessLabel.Cur tml)
        | LhsNext tml -> 
            tml.FindAllIndexExpr |> Seq.iter (addNameRead context node)
            do addWrittenLabel (AccessLabel.Next tml) 

    and internal addNameRead context node trhs =
        let processFields fields =
            fields
            |> List.unzip
            |> snd // here we get a list of all rhs expr used in this literal
            |> List.iter (addNameRead context node)

        match trhs.rhs with
        | RhsCur tml -> 
            // check for array index expressions and recursively call addNameRead on them
            tml.FindAllIndexExpr |> Seq.iter (addNameRead context node)
            // then add all accessed memory (sub-)locations to this node
            do appendAllRead context trhs.Range (AccessLabel.Cur tml) node
        | Prev _ -> () // this is irrelevant for causality
        | FunCall (name, ins, outs) ->
            // add local names for this call
            ins |> List.iter (addNameRead context node)
            outs |> List.iter (addNameWritten context node)
            addSingletonCalls context trhs.Range node name
        | BoolConst _ 
        | IntConst _
        | BitsConst _
        | NatConst _
        | FloatConst _ 
        | ResetConst _ -> ()
        | StructConst structFieldExprList ->
            structFieldExprList |> processFields
        | ArrayConst elems ->
            elems |> processFields
        | Convert (expr, _, _)
        | Bnot expr
        | Neg expr -> addNameRead context node expr
        | Conj (ex1, ex2)
        | Disj (ex1, ex2)
        | Band (ex1, ex2)
        | Bor (ex1, ex2)
        | Bxor (ex1, ex2)
        | Shl (ex1, ex2)
        | Shr (ex1, ex2)
        | Sshr (ex1, ex2)
        | Rotl (ex1, ex2)
        | Rotr (ex1, ex2)
        | Les (ex1, ex2)
        | Leq (ex1, ex2)
        | Equ (ex1, ex2)
        | Add (ex1, ex2)
        | Sub (ex1, ex2)
        | Mul (ex1, ex2)
        | Div (ex1, ex2)
        | Mod (ex1, ex2) ->
            do addNameRead context node ex1
            do addNameRead context node ex2
    
    let internal addRandW context node r w =
        do addNameRead context node r
        do addNameWritten context node w

    
/// This module contains functionality to build program graphs and
/// all functions that deal with parts thereof (nodes, edges).
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module ProgramGraph =
    
    open System.Collections.Generic

    open Blech.Common

    open Blech.Frontend
    open Blech.Frontend.TyChkExpressions
    open Blech.Frontend.CommonTypes
    
    open IntermediateContext


    /// True iff given Edge is a DataFlow link
    let isDataFlow (e: Edge) =
        match e.Payload with
        | DataFlow _ -> true
        | ControlFlow _ | ReturnFlow _ | TerminateThread _ | Tick _ -> false

    /// True iff given Edge is some control flow link (not a tick, not a wr link)
    let isImmediateTransition (e: Edge) =
        match e.Payload with
        | ControlFlow _
        | ReturnFlow _
        | TerminateThread _ -> true
        | DataFlow _ | Tick _ -> false
    
    /// Return all successor nodes reachable via one step of program execution
    /// i.e. we ignore DataFlow transitions in this function
    let cfSucc (node: Node) =
        node.Outgoing
        |> Seq.filter (fun edge -> match edge.Payload with | Transition.DataFlow _ -> false | _ -> true)
        |> Seq.map (fun edge -> edge.Target)

    let private addNode pg payload = pg.Graph.AddNode payload

    let private connectWithTransition transition pg node1 node2 =
        do pg.Graph.AddEdge transition node1 node2

    /// Create a control flow transition without any guard
    let private connect = connectWithTransition (ControlFlow None)

    /// Create a link in the given graph 'pg' from node 'node1' to 'node2'
    /// using a control flow transition with guard 'guard'
    let private guardedConnectWithPrio prio guard = connectWithTransition (ControlFlow (Some (prio,guard)))
    let private guardedConnect = guardedConnectWithPrio 1
    let private tickConnect clock = connectWithTransition (Tick clock)
    let private terminateThreadConnect strength = connectWithTransition (TerminateThread strength)

    /// Replace the Exit location by the other location.
    let private replaceExitBy pg other =
        do pg.Graph.ReplaceNodeBy pg.Exit other

    /// Create a program graph structure without any transitions
    let private createEmpty line thread typ =
        let graph = Graph.Empty ()
        let entry = graph.AddNode {Typ = typ; Line = Some line; Thread = thread}
        let exit =  graph.AddNode {Typ = Location; Line = None; Thread = thread}
        { Entry = entry
          Exit = exit
          Graph = graph }

    /// Generate a program graph for an action (e.g. assignement)
    let private createAction context line thread action =
        let pg = createEmpty line thread (ActionLocation action)
        do connect pg pg.Entry pg.Exit
        match action with
        | Nothing -> ()
        | Action.VarDecl v ->
            let newLhs =
                { lhs = LhsCur (Loc v.name)
                  typ = v.datatype
                  range = v.pos }
            addRandW context pg.Entry v.initValue newLhs
        | Action.ExternalVarDecl v ->
            let newLhs =
                { lhs = LhsCur (Loc v.name)
                  typ = v.datatype
                  range = v.pos }
            addNameWritten context pg.Entry newLhs // no init value to be read
        | Action.Assign (_, tlhs, trhs) -> addRandW context pg.Entry trhs tlhs
        | Action.Assert (_, cond, _)
        | Action.Assume (_, cond, _) -> addNameRead context pg.Entry cond
        | Action.Print (_, _, y) -> y |> List.iter (addNameRead context pg.Entry)
        // function calling
        | Action.FunctionCall (_, name, ins, outs) ->
            // add local names for this call
            ins |> List.iter (addNameRead context pg.Entry)
            outs |> List.iter (addNameWritten context pg.Entry)
            addSingletonCalls context line pg.Entry name
        | Action.Return (_, expr) -> match expr with | Some x -> addNameRead context pg.Entry x | None -> ()
        pg

    /// Generate an unconditional step doing nothing
    let private createNothing context line thread =
        createAction context line thread Nothing

    /// Generate a program graph for the await statement
    let private createAwait context line thread clock cond =
        let pg = createEmpty line thread GuardLocation // dummy node for possible abort after hooks
        let hitawait = addNode pg {Typ = HitAwaitLocation; Line = Some line; Thread = thread}
        do connect pg pg.Entry hitawait
        let startawait = addNode pg {Typ = StartFromAwaitLocation; Line = Some line; Thread = thread}
        do tickConnect clock pg hitawait startawait
        do guardedConnect cond pg startawait pg.Exit 
        do addNameRead context startawait cond
        pg

    /// Generate a program graph for the sequential composition of the
    /// given program graphs
    let private sequentialise pg pgs =
        match pgs with
        | [] -> pg
        | _ ->
            let glue lastGraph nextGraph =
                do replaceExitBy lastGraph nextGraph.Entry
                nextGraph
            let lastGraph = List.fold glue pg pgs
            let allGraphs =
                pg :: pgs 
                |> List.map (fun pg -> pg.Graph)
                |> Graph.JoinAll
            { Entry = pg.Entry
              Exit = lastGraph.Exit
              Graph = allGraphs }

    /// Generate a program graph for an activity call
    /// Creates a separate Action.VarDecl for a fresh location receiver
    let private createActCall context line thread (pos, name, optReceiver: Receiver option, inputs, outputs) termVar =
        let retvar = 
            match optReceiver with
            | Some (FreshLoc varDecl) ->
                Some { lhs = LhsCur (Loc varDecl.name); typ = varDecl.datatype; range = varDecl.pos }
            | Some (UsedLoc tlhs) -> 
                Some tlhs
            | Some (ReturnLoc tlhs) ->
                Some tlhs
            | None -> 
                None

        let pgAwait = createAwait context line thread "ticker" {rhs = BoolConst true; typ = ValueTypes BoolType; range = line}

        let pg = createEmpty line thread (CallInit (pos, name, retvar, inputs, outputs, termVar))
        let callNode = addNode pg {Typ = CallNode(pos, name, retvar, inputs, outputs, termVar); Line = Some line; Thread = thread}
                
        do connect pg pg.Entry pgAwait.Entry
        do replaceExitBy pgAwait callNode
        let termVarExpr = {rhs = RhsCur(Loc termVar); typ = ValueTypes (IntType Int32); range = line}
        let zeroExpr = {rhs = IntConst Int.Zero32 ; typ = ValueTypes (IntType Int32); range = line}
        let termCond = {rhs = Equ (zeroExpr, termVarExpr); typ = ValueTypes BoolType; range = line}
        do guardedConnect termCond pg callNode pg.Exit
        let pauseCond = { termCond with rhs = unsafeNeg termCond }
        do guardedConnect pauseCond pg callNode pgAwait.Entry

        // We do not check that the output variables are mutually different (non-aliasing)
        // This is handled later by the causality check
        inputs |> List.iter (addNameRead context pg.Entry)
        outputs |> List.iter (addNameWritten context pg.Entry)
        retvar |> Option.iter (addNameWritten context pg.Entry)
        inputs |> List.iter (addNameRead context callNode)
        outputs |> List.iter (addNameWritten context callNode)
        retvar |> Option.iter (addNameWritten context callNode)

        addSingletonCalls context line pg.Entry name
        addSingletonCalls context line callNode name
                
        let pgActCall = { pg with Graph = Graph.JoinAll [pg.Graph; pgAwait.Graph] }

        match optReceiver with
        | Some (FreshLoc vdecl) -> 
            let pgVarDecl = createAction context vdecl.pos thread (Action.VarDecl vdecl) 
            sequentialise pgVarDecl [pgActCall]
        | Some _
        | None ->
            pgActCall
    

    /// Generate program graph for strong delayed abort
    let private createAbortBefore context pos thread bodyGenerator abortCond =
        let pgAwait = createAwait context pos thread "ticker" {rhs = BoolConst true; typ = ValueTypes BoolType; range = pos}
        
        let graph = Graph.Empty ()
        let abortDecisionPoint = graph.AddNode {Typ = GuardLocation; Line = None; Thread = thread}
        let entry = graph.AddNode {Typ = AbortBegin (pgAwait.Entry, abortDecisionPoint); Line = Some pos; Thread = thread}
        let subPg = bodyGenerator entry // Generate subgraphs where the thread IDs are derived from thread of entry
        let abortEnd = graph.AddNode {Typ = AbortEnd subPg.Exit; Line = None; Thread = thread}
        let exit = graph.AddNode {Typ = Location; Line = None; Thread = thread}
        let pg =
            { Entry = entry
              Exit = exit
              Graph = graph }

        do connect pg abortEnd exit
        
        do replaceExitBy pgAwait abortDecisionPoint
        do guardedConnect abortCond pg abortDecisionPoint abortEnd
        let negCond = { abortCond with rhs = unsafeNeg abortCond }
        do guardedConnect negCond pg abortDecisionPoint pgAwait.Entry 
        do addNameRead context abortDecisionPoint abortCond        
        
        do connect pg pg.Entry subPg.Entry  // connect abort head to start of body
        do connect pg subPg.Exit abortEnd // connect body's end to the abort end node
                
        { pg with Graph = Graph.JoinAll [pg.Graph; pgAwait.Graph; subPg.Graph] }

    

    /// Returns program graph for if cond then pg1 else pg2
    let private createIf context line thread cond pg1 pg2  =
        let pg = createEmpty line thread GuardLocation
        let negCond = { cond with rhs = unsafeNeg cond }
        do guardedConnect cond pg pg.Entry pg1.Entry 
        do guardedConnect negCond pg pg.Entry pg2.Entry 
        do replaceExitBy pg1 pg.Exit // this automatically joins the two branches
        do replaceExitBy pg2 pg.Exit
        do addNameRead context pg.Entry cond
        { pg with Graph = Graph.JoinAll [pg.Graph; pg1.Graph; pg2.Graph] }

    /// Generate Repeat P Until C
    let private createRepeatUntil context line thread cond subPg =
        let pg = createEmpty line thread Location
        let guardNode = addNode pg {Typ = GuardLocation; Line = Some line; Thread = thread}
        let negCond = {cond with rhs = unsafeNeg cond}
        do guardedConnect cond pg guardNode pg.Exit
        do connectWithTransition (ReturnFlow (1,negCond)) pg guardNode pg.Entry // ReturnFlow transitions are key to a loop-free block graph,
                                                                                // repetition is realised with a goto in the generated C code
        do connect pg subPg.Exit guardNode
        do connect pg pg.Entry subPg.Entry
        do addNameRead context guardNode cond
        { pg with Graph = Graph.Join pg.Graph subPg.Graph }
        
    /// Generates the parallel composition of all program graphs in pgs
    let private createCobegin context line thread blocks termVar =
        let pgAwait = createAwait context line thread "ticker" {rhs = BoolConst true; typ = ValueTypes BoolType; range = line}
        
        let graph = Graph.Empty ()
        let joinNode = graph.AddNode {Typ = JoinLocation termVar; Line = None; Thread = thread}

        let entry = graph.AddNode {Typ = CobeginLocation joinNode; Line = Some line; Thread = thread}
        let exit = graph.AddNode {Typ = Location; Line = None; Thread = thread}
        let newPg =
            { Entry = entry
              Exit = exit
              Graph = graph }
        let graphs =
            [
                for (strength, pgOfFork) in blocks do
                    let pg = pgOfFork entry // Generate subgraphs where the thread IDs are derived from thread of entry
                    do connect newPg newPg.Entry pg.Entry // connect cobegin fork to each sub thread
                    do terminateThreadConnect strength newPg pg.Exit joinNode // connect each thread's end to the join node
                    // we do not connect inner nodes to the join node here; this would lead to spurious cycles in the causality analysis
                    // instead the contruction of the block will make sure that inner nodes have precedence over the resp. join node (block)
                    yield pg.Graph // return the program graph of the subthread
            ]
        
        do replaceExitBy pgAwait joinNode
        let termCond = {rhs = RhsCur(Loc termVar); typ = ValueTypes (BoolType); range = line}
        do guardedConnect termCond newPg joinNode newPg.Exit
        let pauseCond = { termCond with rhs = unsafeNeg termCond }
        do guardedConnect pauseCond newPg joinNode pgAwait.Entry
        
        { newPg with Graph = Graph.JoinAll (newPg.Graph :: pgAwait.Graph :: graphs) }

    /// Helper function for createPGofStmt.
    /// Creates a helper variable to store some extra information about the control flow.
    let private createHelperVariable context pos name dty =
        let qname = mkIndexedAuxQNameFrom name
        TyChkAmendment.getDefaultValueFor pos name dty |> function
        | Ok initVal ->
            try
                let v = 
                    { VarDecl.pos = pos
                      name = qname
                      datatype = dty
                      mutability = Mutability.Variable
                      initValue = initVal
                      annotation = Attribute.VarDecl.Empty
                      allReferences = HashSet() }
                TypeCheckContext.addDeclToLut context.lut qname (Declarable.VarDecl v)
                v
            with _ -> 
                failwith <| sprintf "Temporary variable %s already exists." (qname.ToString())
        | Error _ ->
            failwith <| sprintf "Could not determine default value for type %s." (dty.ToString())
        
    /// Generates a program graph for a given statement
    let rec private createPGofStmt context thread stmt =
        match stmt with
        // local variable or object declaration
        | Stmt.VarDecl v -> createAction context v.pos thread (Action.VarDecl v)
        | Stmt.ExternalVarDecl v -> createAction context v.pos thread (Action.ExternalVarDecl v)
        // actions
        | Stmt.Assign (pos, tlhs, trhs) -> createAction context pos thread (Action.Assign (pos, tlhs, trhs))
        | Stmt.Assert (pos, cond, x) -> createAction context pos thread (Action.Assert (pos, cond, x))
        | Stmt.Assume (pos, cond, x) -> createAction context pos thread (Action.Assume (pos, cond, x))
        | Stmt.Print (pos, x, y) -> createAction context pos thread (Action.Print (pos, x, y))
        // pause
        | Await (pos, cond) -> createAwait context pos thread "ticker" cond
        // control flow
        | ITE (pos, cond, stmts1, stmts2) -> // line, condition, if-block, else-block (each possibly empty!)
            let pg1 = createPGofBody context pos thread stmts1 
            let pg2 = createPGofBody context pos thread stmts2  
            createIf context pos thread cond pg1 pg2 
        | Stmt.Return (pos, expr) -> createAction context pos thread (Action.Return (pos, expr))
        | Cobegin (pos, blocks) -> // line, list of threads each being weak/strong with a code block
            // genNewThread generates new child threads from THIS thread
            let genNewThread = Thread.newChildThread thread
            // using genNewThread, translateSubProg knows how to create a PG for a code block
            let translateSubProg = (fun stmts forkNode -> createPGofBody context pos (genNewThread forkNode) stmts)
            // finally this is wrapped in blocksDependingOnFork therby resolving the cyclic dependecy between createCobegin and createPGofBody
            let blocksDependingOnFork = blocks |> List.map (fun (strength, stmts) -> strength, translateSubProg stmts)
            
            let v = createHelperVariable context pos "termVar" (ValueTypes(IntType Int32))
            createCobegin context pos thread blocksDependingOnFork v.name
        | WhileRepeat _ -> // unreachable code since the type checker rewrites while into repeat
            failwith "replace while by repeat"
        | RepeatUntil (pos, body, cond, _) ->
            createPGofBody context pos thread body
            |> createRepeatUntil context pos thread cond
        | Preempt (pos, preemption, cond, moment, body) -> // line, kind of preemption, abort condition, moment of preemption, body
            match preemption with
            | Abort ->
                match moment with
                // abort after was stripped from the syntax but still exists as a data structure
                | Moment.After -> 
                    //let branches =
                    //    [ Weak, body
                    //      Weak, [Await(pos, cond)] ]
                    //createPGofStmt context thread (Cobegin (pos, branches))
                    failwith "Abort after does not exist. It was replaced by explicit cobegin weak."
                | Moment.Before ->
                    // this is the only alive code path for the Abort case
                    let genNewThread = Thread.newChildThread thread
                    // using genNewThread, translateSubProg knows how to create a PG for a code block
                    let translateSubProg = (fun stmts forkNode -> createPGofBody context pos (genNewThread forkNode) stmts)
                    createAbortBefore context pos thread (translateSubProg body) cond 
                | Moment.OnNext -> failwith "Cannot handle OnNext"
            | Reset ->
                failwith "Reset should be transformed away before."
            | Suspend -> // does not exists in the current syntax but still lives as a data structure
                failwith "Suspending is a bad idea."
        // scoping
        | StmtSequence body -> createPGofBody context Range.range0 thread body // range0 is a dummy which is only used if body is empty
        // calling 
        // all files should be processed in order, thus the subprogram 
        // called here must be in the context already
        // just generate a call node
        | ActivityCall (pos, name, retvar, inputs, outputs) ->
            let v = createHelperVariable context pos "retcode" (ValueTypes(IntType Int32))
            createActCall context pos thread (pos, name, retvar, inputs, outputs) v.name
        | Stmt.FunctionCall (pos, name, inputs, outputs) ->
            createAction context pos thread (Action.FunctionCall(pos, name, inputs, outputs))

    and private createPGofBody context pos thread body =
        // Process the activity's body
        List.map (createPGofStmt context thread) body
        |> function
            | [] -> createNothing context pos thread // create an empty statement graph with position information of the surrounding statement
            | pg :: pgs -> sequentialise pg pgs

    let private createPGofActivity (context: IntermediateContext) thread subProg =
        let context = context.ReInitNodeDicts()
        let pg = createPGofBody context Range.range0 thread subProg.body
        do context.pgs.Add(subProg.Name, pg)
        do context.subprogReadNodes.Add(subProg.Name, context.tempNameReadByNodes)
        do context.subprogWrittenNodes.Add(subProg.Name, context.tempNameWrittenByNodes)
        
    /// Given a package, translates all its activities to program graphs
    /// and populates an intermediateContext
    let createPGofPackage (lut, pack) =
        let context = IntermediateContext.Empty(lut)
        for subProg in pack.funacts do
            let thread = Thread.newThread()
            // filter away functions, since their prog graph is useless, 
            // and causes spurious causality errors
            if not subProg.IsFunction then
                do createPGofActivity context thread subProg
        context

    /// Given two nodes check if they are concurrent
    let areConcurrent (node1: Node) (node2: Node) =
        Thread.areConcurrent node1.Payload.Thread node2.Payload.Thread

    /// Find least common fork (may not exist if root is the lca)
    let internal leastCommonFork (node1: Node) (node2: Node) = 
        let isForkItself n =
            match node1.Payload.Typ with
            | LocationType.CobeginLocation _ -> true
            | _ -> false
        let f1 = 
            [if isForkItself node1 then node1]
            @ Thread.allForks node1.Payload.Thread
        let f2 =
            [if isForkItself node2 then node2]
            @ Thread.allForks node2.Payload.Thread
        f1 |> List.tryFind (fun f -> List.contains f (f2))
    
    let memoizedCycles = Dictionary<QName, ResizeArray<Dictionary<Node,Node>*Graph>>()

    /// Given two nodes check if they are both in the surface or depth 
    /// wrt. to their common root thread or not
    let areBothInSurfOrDepth name graph (node1: Node) (node2: Node) =
        let allCycles () = 
            match memoizedCycles.TryGetValue name with
            | true, cycles -> cycles
            | false, _ ->
                let cycles = GenericGraph.johnson75 graph
                memoizedCycles.Add(name, cycles)
                cycles
        if areConcurrent node1 node2 then
            // find least common fork (may not exist if root is the lca)
            let lcf = 
                leastCommonFork node1 node2
                |> Option.get // must exist, we have checked that node1 and node2 are concurrent
            // find all paths from lcf to given node and check if there is one with a tick edge
            let existsOrAlwaysPausesTowards node =
                let allLcfToNode = 
                    GenericGraph.allSimplePaths cfSucc lcf node
                    |> List.filter (Seq.isEmpty >> not) // why is it at all possible to get empty paths here?
                let allLoopsWithinLcfThread = 
                    allCycles()
                    |> Seq.choose (fun (mapping, g) -> if mapping.ContainsKey node then Some (g.Nodes |> Seq.toList) else None)
                    |> Seq.toList
                    |> List.filter (List.forall(fun n -> Thread.strictlyContains lcf.Payload.Thread n.Payload.Thread)) // loops that do not leave the enclosing cobegin
                    |> List.filter (Seq.isEmpty >> not) // why is it at all possible to get empty paths here?
                    
                let pathToPause =
                    [ allLcfToNode
                      allLoopsWithinLcfThread ]
                    |> Seq.concat
                    |> Seq.map (fun path -> // for every path
                        path |> Seq.exists (fun (n: Node) -> // for every node
                            match n.Payload.Typ with
                            | StartFromAwaitLocation _ -> true
                            | _ -> false
                            )
                        ) 
                ( pathToPause |> Seq.contains true,
                  pathToPause |> Seq.forall id )

            // find all paths from lcf to node1 and check if there is one with a tick edge
            let hasPauseTowardsNode1, alwaysPauseTowardsNode1 = existsOrAlwaysPausesTowards node1
                
            // find all paths from lcf to node2 and check if there is one with a tick edge
            let hasPauseTowardsNode2, alwaysPauseTowardsNode2 = existsOrAlwaysPausesTowards node2
                
            // return false if one is only in surface and the other only in depth
            let node1OnlyInSurface = not hasPauseTowardsNode1
            let node1OnlyInDepth = alwaysPauseTowardsNode1
            let node2OnlyInSurface = not hasPauseTowardsNode2
            let node2OnlyInDepth = alwaysPauseTowardsNode2
            
            ((node1OnlyInSurface && node2OnlyInDepth) || (node1OnlyInDepth && node2OnlyInSurface))
            |> not
        // if not concurrent there is no sense to talk about surface and depth
        else false

    
