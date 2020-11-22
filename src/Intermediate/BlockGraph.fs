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

module Blech.Intermediate.BlockGraph

open System.Collections.Generic

open Blech.Common
open Blech.Common.Range
open Blech.Frontend.CommonTypes

module GenericGraph = Blech.Common.GenericGraph


/// A Block begins if a node has more than one incoming (control flow or dataflow) edge
/// A Block ends if a node has more than one outgoing control flow edges
/// Blocks are split at the Tick transition
/// Each node belongs to exactly one Block.
type Block =
    { innerNodes: ResizeArray<Node>
      mutable Priority: int }
    override this.ToString() =
        let line (x : range option)=
            match x with
            | None -> ""
            | Some l -> (l.StartLine).ToString()

        let pp loc =
            let pos = line loc.Line
            let threadid = loc.Thread.ID.ToString()
            let typ =
                match loc.Typ with
                | HitAwaitLocation _ -> "hit"
                | StartFromAwaitLocation _ -> "start"
                | ActionLocation _ -> "act"
                | Location -> "loc"
                | CallInit _ -> "clinit"
                | CallNode _ -> "call"
                | GuardLocation -> "guard"
                | CobeginLocation _ -> "cobegin"
                | JoinLocation _ -> "join"
                | AbortBegin _ -> "abortBegin"
                | AbortEnd _ -> "abortEnd"
            pos + " _|" + threadid + "|_" + ", " + typ + "\\n"
            
        let nodes = 
            this.innerNodes
            |> Seq.map (fun node -> pp node.Payload)
            |> Seq.reduce (+)

        let prio = this.Priority.ToString()
            
        "[label=\"" + nodes + prio + "\"]"

    static member Empty () = { innerNodes = ResizeArray(); Priority = 0 }


type Edge =
    | Edge
    override this.ToString() = ""


type BlockNode = GenericGraph.Node<Block,Edge>
type BlockEdge = GenericGraph.Edge<Block,Edge>
type BlockGraph = GenericGraph.Graph<Block,Edge>


type T =
    { blockGraph: BlockGraph
      node2BlockNode: Dictionary<Node, BlockNode> }
    static member Empty () =
        {
            blockGraph = BlockGraph.Empty()
            node2BlockNode = Dictionary<Node, BlockNode>()
        }


let private closeBlock context block = 
    //if this is a non-empty block
    if block.innerNodes.Count > 0 then 
        // then add it to the graph
        let blockNode = context.blockGraph.AddNode block 
        // and put all its nodes to the mapping Nodes -> BlockNodes
        block.innerNodes |> Seq.iter (fun node -> context.node2BlockNode.Add(node, blockNode))
            

let rec private bfs context (queue: ResizeArray<Node>) (visited: HashSet<Node>) curBlock =
    if queue.Count = 0 then
        closeBlock context curBlock
    else
        let head = queue.[0]
        queue.Remove head |> ignore
        let theBlock =
            if Seq.length head.Incoming > 1 then // this also takes into account dependency edges and thus also splits because we might need to reschedule here
                closeBlock context curBlock
                Block.Empty()
            else
                curBlock
        theBlock.innerNodes.Add head
        visited.Add head |> ignore
                
        // prepend all unvisited successors of head to the queue
        let allSuccs = head |> ProgramGraph.cfSucc 
            
        let newSuccs =
            allSuccs
            |> Seq.filter (fun succ -> not (visited.Contains succ) && not (queue.Contains succ)) // only add the non-visited successors to the queue
                                                                                                 // also do not add nodes that are already in the queue once again
            |> Seq.toList // strangely this is needed since otherwise after adding the elements to the queue newSuccs is empty
        newSuccs |> Seq.iter (fun succ -> queue.Insert(0,succ))
        if Seq.isEmpty newSuccs || Seq.length allSuccs > 1 then // if we found no new successor or more than one successor
            closeBlock context theBlock
            bfs context queue visited (Block.Empty())
        elif head.Payload.Typ.hasAbortBegin then // if current node is an abort head
            closeBlock context theBlock
            bfs context queue visited (Block.Empty())
        else
            // continue with curBlock UNLESS the successor is a StartFromAwaitLocation node
            let theSuccessor = Seq.tryHead newSuccs |> Option.defaultValue (Seq.head allSuccs)
            match theSuccessor.Payload.Typ with
            | StartFromAwaitLocation _ ->
                closeBlock context theBlock
                bfs context queue visited (Block.Empty())
            | _ ->
                bfs context queue visited theBlock

/// True for data flow and control flow and terminate thread edges
/// False for tick and return edges
let private filterDataFlowAndImmediate (edge: GenericGraph.Edge<Location,Transition>) =
    match edge.Payload with 
    | Tick _ -> false               // always discard time step edges
    | ReturnFlow _ -> false // remove edges back to loop heads
    | _ -> true

// connect blocks with control flow and data flow edges
let private connections context = 
    context.blockGraph.Nodes
    |> Seq.collect (fun block -> 
        block.Payload.innerNodes 
        |> Seq.collect (fun node -> 
            node.Outgoing
            |> Seq.filter filterDataFlowAndImmediate // Tick edges are ignored in the BlockGraph
                                                     // Reversing Tick edges here would be really wrong
            |> Seq.map (fun edge ->
                    block, context.node2BlockNode.[edge.Target]
                )
            )
        )


/// Perform BFS
let buildFromPG (pg: ProgramGraph) =
    let context = T.Empty()
    let visited = HashSet<Node>()
    
    let rec walkFrom nodeToStartWith =
        let initQueue = ResizeArray<Node>()
        initQueue.Add(nodeToStartWith) |> ignore
        bfs context initQueue visited (Block.Empty())
        // compute set of unreachable control flow graph nodes
        let unreachSet = pg.Graph.Nodes |> Seq.except visited
        if Seq.isEmpty unreachSet then ()
        else Seq.head unreachSet |> walkFrom
        
    do walkFrom pg.Entry
    
    connections context
    |> Seq.iter (fun (a,b) -> if a <> b then context.blockGraph.AddEdge Edge a b)


    // Add connections between blocks that represent the fact that subthreads
    // must have done a tick before the containing thread performs a tick
    //
    // Def: - a block "belongs to thread T" if the entry node of this block
    //        belongs to thread T (anyway all nodes belong to the same thread
    //        inside a block, since a block cannot cross thread boundaries
    //        as this requires a fork or join node which by definition close
    //        or open blocks)
    //      - a block ends thread T if its entry node is a JoinLocation
    // Hence, add an edge from every block in thread T to the block that ends T
    
    let endOfT =
        context.blockGraph.Nodes 
        |> Seq.filter (fun block ->
            match block.Payload.innerNodes.[0].Payload.Typ with 
            | JoinLocation _ -> true 
            | _ -> false
            ) 
        |> Seq.toList
    
    for block in context.blockGraph.Nodes do
        let forkOpt = block.Payload.innerNodes.[0].Payload.Thread.Fork
        match forkOpt with
        | None -> () // nothing to do for root thread
        | Some fork ->
            match fork.Payload.Typ with
            | CobeginLocation joinNode ->
                // find the "joinBlock" that contains this joinNode
                // and add link from block to joinBlock
                context.blockGraph.Nodes 
                |> Seq.tryFind (fun someBlock -> someBlock.Payload.innerNodes.[0] = joinNode)
                |> function
                    | Some joinBlock -> 
                        context.blockGraph.AddEdge Edge block joinBlock // add edge
                    | None ->
                        // impossible, by construction, if a thread has an ancestor there should be a corresponding parent thread join
                        failwith "No ancestor join block was found!"
            | AbortBegin (_, decisionNode) ->
                // make sure abort decision is done before anything in the body
                context.blockGraph.Nodes 
                |> Seq.tryFind (fun someBlock -> someBlock.Payload.innerNodes.[0] = decisionNode)
                |> function
                    | Some decisionBlock -> 
                        context.blockGraph.AddEdge Edge decisionBlock block // add edge
                    | None ->
                        // impossible, by construction, if a thread has an ancestor there should be a corresponding parent thread join
                        failwith "No ancestor decision block was found!"
            | _ -> failwith "A fork node must contain a CobeginLocation payload."
    context

let bgCtxOfPGs (pgs: Dictionary<QName, ProgramGraph>) =
    let blockGraphContext = Dictionary<QName, T>()
    for kvp in pgs do
        blockGraphContext.Add(kvp.Key, buildFromPG kvp.Value)
    blockGraphContext
        

// given the block graph, schedule it using topological sort
let assignPriorities graph =
    let hasCycle, ordering = GenericGraph.topologicalSort graph
    if hasCycle then
        Logging.log4 "translateActivity" ("block graph\n" + graph.ToString())
        failwith "IMPOSSIBLE!!! The graph of blocks has a cycle!!!"
    else
        for i in 0..(ordering.Count - 1) do
            ordering.[i].Payload.Priority <- (i + 1)
