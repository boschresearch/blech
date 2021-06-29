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

namespace Blech.Backend

open System.Collections.Generic

open Blech.Common.PPrint

open Blech.Frontend
open Blech.Frontend.CommonTypes
open Blech.Frontend.BlechTypes

open Blech.Intermediate


type Action = Blech.Intermediate.Action


/// Program counters are hierarchically represented in a tree structure
/// The root node is the main program counter of an activity
/// Other nodes represent pcs for cobegin branches
/// The pcs for a called subactivity are not part of this tree, they are
/// stored in subcontexts
type PCtree =
    {
        mainpc: ParamDecl
        thread: Thread
        subPCs: PCtree list
    }
    /// Flattens the program counter tree to a list
    /// starting with this.mainpc first.
    member this.AsList =
        this.mainpc :: (this.subPCs |> List.collect (fun p -> p.AsList))
    member this.Contains (pc: ParamDecl) =
        this.AsList 
        |> List.exists (fun p -> p.name = pc.name) 
    member this.SubTreeForThread t =
        if this.thread = t then Some this
        else
            this.subPCs 
            |> List.map (fun s -> s.SubTreeForThread t) 
            |> List.tryFind (Option.isSome)
            |> Option.defaultValue None


/// An activity context represents the static data of an activity and
/// of called subactivities.
/// Inputs, outputs and retvar are not part of the context because they
/// need no static representation.
type ActivityContext =
    {
        locals: ParamDecl list
        pcs: PCtree // tree for THIS activity only
        // Sub-context is identified by a program counter name and a callee name
        subcontexts: Set<string * QName>
    }


type Compilation =
    {
        name: QName
        inputs: ParamDecl list
        outputs: ParamDecl list
        retvar: ParamDecl option
        actctx: ActivityContext option // None for functions
        varsToPrev: QName list // always empty for functions
        signature: Doc // C prototype, goes into *.h
        implementation: Doc // pretty printed C code
        doc: Doc option // optional "doc"-comment
    }
    member this.GetActCtx =
        match this.actctx with
        | Some x -> x
        | None -> failwith "Tried to access activity context where there is none. Is this Compilation a function?"


type TranslationContext = {
    tcc: TypeCheckContext
    pgs: Dictionary<QName, ProgramGraph>
    bgs: Dictionary<QName, BlockGraph.T>
    compilations: Compilation list
    cliContext: Blech.Common.Arguments.BlechCOptions
}


[<AutoOpen>]
module Utils =
    /// Prepends item to items only if it is not already there.
    let internal addUniqueParam (item: ParamDecl) (items: ParamDecl list) =
        items 
        |> List.map (fun p -> p.name)
        |> List.contains item.name
        |> function
            | true -> items
            | false -> items @ [item]


[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module PCtree =
    
    let internal mkNew thread pc = 
        {mainpc = pc; thread = thread; subPCs = []}
    
    let internal addPCtree tree subtree = 
        {tree with PCtree.subPCs = tree.subPCs @ [subtree]} // keep in order
    
    let internal asList (tree: PCtree) = tree.AsList

    let internal add tree (thread: Thread) (pc: ParamDecl) =
        let transplant dest child =
            {dest with subPCs = dest.subPCs @ [child]}
        let rec insertIntoTree tr ancs =
            // ancs - ancestors sorted from root to current thread
            assert (tr.thread = List.head ancs)
            let nextThread = List.head (List.tail ancs)
            tr.subPCs
            |> List.tryFindIndex (fun subtree -> subtree.thread = nextThread)
            |> function
                | Some index ->
                    let subtree = insertIntoTree tr.subPCs.[index] (List.tail ancs)
                    let newSubPCs = tr.subPCs.[0..index-1] @ [subtree] @ tr.subPCs.[index+1..]
                    { tr with subPCs = newSubPCs }
                | None ->
                    // make new subtree for pc
                    let newSubtree = mkNew thread pc
                    // transplant every pc that is in a subthread underneath
                    let subTreesToMove, subTreesUnaffected =
                        tr.subPCs
                        |> List.partition (fun subtree -> List.contains nextThread (Thread.allAncestors subtree.thread))
                    let finalSubtree = List.fold (transplant) newSubtree subTreesToMove
                    let newSubPCs = subTreesUnaffected @ [finalSubtree]
                    { tr with subPCs = newSubPCs }        
        let alreadyAdded =
            tree.subPCs |> List.exists (fun t -> t.Contains pc)
        if alreadyAdded then 
            tree // nothing to do
        else
            let allAncestors = Thread.allAncestors thread |> List.rev // sort from root to current thread
            insertIntoTree tree allAncestors


[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module ActivityContext =
    
    let internal mkNew thread mainpc = 
        {locals = []; pcs = PCtree.mkNew thread mainpc; subcontexts = Set.empty}
    
    let internal addLocal local ctx = 
        {ctx with ActivityContext.locals = addUniqueParam local ctx.locals}
    
    let internal addSubContext ctx pcName calleName = 
        {ctx with ActivityContext.subcontexts = 
                  ctx.subcontexts.Add(pcName, calleName)} // keep in order


[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Compilation =

    let mkNew name =
        {
            name = name
            inputs = []
            outputs = []
            retvar = None
            actctx = None
            varsToPrev = []
            signature = empty
            implementation = empty
            doc = None
        }

    let internal addLocal comp local = 
        { comp with Compilation.actctx = 
                    comp.GetActCtx 
                    |> (ActivityContext.addLocal local) 
                    |> Some }

    let internal addSubContext comp pcName calleName =
        { comp with Compilation.actctx = 
                    ActivityContext.addSubContext comp.GetActCtx pcName calleName 
                    |> Some }

    /// Add program counter to this computation's activity context
    /// the block determines where in the PC tree to put it
    /// based on thread relationships
    let internal addPc comp thread pc =
        match comp.actctx with
        | None ->
            // assert that the first added pc is the main pc
            // (the main thread has no ancestors)
            assert thread.Ancestor.IsNone
            { comp with actctx = ActivityContext.mkNew thread pc |> Some }
        | Some ac ->
            // if this function has been called for another block
            // in the same thread then the given pc will already
            // be in the tree - simply do nothing
            if ac.pcs.Contains pc then comp 
            else
                // assert that the newly added pc is NOT the main pc
                assert thread.Ancestor.IsSome
                let newTree = PCtree.add ac.pcs thread pc
                let newAc = {ac with pcs = newTree}
                { comp with actctx = newAc |> Some }