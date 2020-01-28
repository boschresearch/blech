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

/// This name space contains closely related types which are needed for program
/// graph generation, representation of read write dependecies and causality
/// checking.
/// 
/// MemoryLabels - distinguish typed memory locations (from BlechTypes) by the
///                point in time they are accessed (current, previous, next)
/// Transition
/// Location
/// Thread
/// ProgramGraph
/// IntermediateContext
namespace Blech.Intermediate

open System.Collections.Generic

open Blech.Common.Range

open Blech.Frontend
open Blech.Frontend.CommonTypes
open Blech.Frontend.BlechTypes

module GenericGraph = Blech.Common.GenericGraph


/// Identifies a section of memory by a time point and typed memory location
type AccessLabel =
    | Cur of TypedMemLoc
    | Prev of TypedMemLoc
    | Next of TypedMemLoc
    | SubProg of QName
    override this.ToString() = 
        match this with 
        | Cur tml -> tml.ToBasicString()
        | Prev tml -> "prev " + tml.ToBasicString()
        | Next tml -> "next " + tml.ToBasicString()
        | SubProg name -> name.ToString()


/// May later be used to distinguish awaits in different clocks
/// Currently rather useless, since its always set to "ticker" 
/// in ProgramGraph.createPGofStmt
type private Clock = string


/// Transitions that come from the program are control flow edges (which are possibly guarded) as well as tick edges and terminate thread edges
/// DataFlow edges indicate write-read precedence between nodes and are added by causality analysis
type Transition = 
    | ControlFlow of (int * TypedRhs) option // possible guard with priority 1 low (default), the larger number the higher the priority
    | ReturnFlow of (int * TypedRhs) // special edge going back to head of return statement
    | Tick of Clock
    | DataFlow of AccessLabel * range * range // memory location that is written and read
    | TerminateThread of Strength
    override this.ToString() =
        match this with
        | ReturnFlow (prio,guard)
        | ControlFlow (Some (prio,guard)) ->
            sprintf "[label=\"%s: %s\"]" (string prio) (guard.ToString())
        | ControlFlow None -> ""
        | Tick clock -> sprintf "[label=\"%s\"]" (clock.ToString())
        | DataFlow (m,_,_) -> sprintf "[style = dashed, color = orange, fontcolor = orange, label=\"wr: %s\"]" (m.ToString())
        | TerminateThread str ->
            match str with 
            | Weak -> "[label=\"weak\"]" 
            | Strong -> "[label=\"strong\"]"


/// These are typed, atomic statements,
/// i.e. statements that cannot be subdivided and that are
/// executed instantaneously
type Action =
    | Nothing
    // initialisation
    | VarDecl of VarDecl
    | ExternalVarDecl of ExternalVarDecl
    // actions
    | Assign of range * TypedLhs * TypedRhs
    | Assert of range * TypedRhs * string
    | Assume of range * TypedRhs * string
    | Print of range * string * (TypedRhs list)
    // function calling
    | FunctionCall of range * QName * TypedRhs list * TypedLhs list // line, who to call, inputs, outputs
    | Return of range * TypedRhs option // line, expressions to return


/// The different kinds of Locations
type LocationType = 
    | HitAwaitLocation // Here a reaction ends
    | StartFromAwaitLocation // Here a reaction starts
    | ActionLocation of Action // Location that represents an atomic Blech statement
    | Location // Dummy location for control flow
    | CallInit of range * QName * TypedLhs option * TypedRhs list * TypedLhs list * QName
    | CallNode of range * QName * TypedLhs option * TypedRhs list * TypedLhs list * QName
        // Location that represents an activity call which is NOT an atomic statement and thus not covered by Action
    | AbortEnd of HashSet<GenericGraph.Node<Location, Transition>>
    | GuardLocation
    | CobeginLocation of GenericGraph.Node<Location, Transition>
    | JoinLocation of QName


/// Locations represent statements or parts thereof
and Location =
    { Typ : LocationType
      Line: range option
      Thread: Thread }
with
    override this.ToString() =
        let line =
            match this.Line with
            | None -> ""
            | Some srcPos -> (srcPos.StartLine).ToString()
        let label = 
            match this.Typ with
            | StartFromAwaitLocation ->
                "shape = box, style = filled, fillcolor = darkgreen, fontcolor = white, label = \"" 
                + line + " _|" 
                + this.Thread.ID.ToString() + "|_ " 
                + "\""
            | HitAwaitLocation _ -> 
                "shape = box, style = filled, fillcolor = darkgreen, fontcolor = white, label = \"" 
                + line + " _|" 
                + this.Thread.ID.ToString() + "|_\""
            | CallInit _ ->
                "shape = box, style = filled, fillcolor = yellow, fontcolor = black, label = \"" 
                + line + " _|"
                + this.Thread.ID.ToString() + "|_ call init\""
            | CallNode (_, name, _, _, _, _) -> 
                "shape = box, style = filled, fillcolor = yellow, fontcolor = black, label = \"" 
                + line + " _|"
                + this.Thread.ID.ToString() + "|_ "
                + name.ToString() + "\""
            | CobeginLocation _ -> 
                "shape = house, style = filled, fillcolor = darkorchid1, fontcolor = black, label = \""
                + line + " _|" + this.Thread.ID.ToString() + "|_\""
            | JoinLocation _ -> 
                "shape = invhouse, style = filled, fillcolor = darkorchid1, fontcolor = black, label = \""
                + line + " _|" + this.Thread.ID.ToString() + "|_\""
            | Location
            | GuardLocation
            | ActionLocation _ -> // TODO: show abbreviated guard or action
                "label = \"" + line + " _|" 
                + this.Thread.ID.ToString() + "|_" + "\""
            | AbortEnd _ -> 
                "shape = egg, style = filled, fillcolor = burlywood3, fontcolor = black, label = \""
                + line + " _|" + this.Thread.ID.ToString() + "|_ abort end\""
            
        "[" + label + "]"


/// Every location belongs to a thread. Threads allow to determine which locations are
/// statically concurrent. This is required for causality analysis.
and Thread = 
    { Fork: GenericGraph.Node<Location, Transition> option //pointer to immediate ancestor
      ID: int
      Ancestor: Thread option } // TODO make Ancestor a property, since it can be deduced from the Fork (and if there is no fork, there is no ancestor, too)


// In this module we distinguish between a Node and a Location.
// A Node is part of the graph structure. It carries a Location
// as its payload. Thus Location summarises the data that is attached
// to a Node.
// The same applies to Edge and Transition.
type Node = GenericGraph.Node<Location, Transition>
type Edge = GenericGraph.Edge<Location, Transition>
type Graph = GenericGraph.Graph<Location, Transition>


/// Instances of ProgramGraph are the building blocks of the control flow
/// graph. Each ProgramGraph has a unique entry and a unique exit node.
/// ProgramGraphs can be composed according to control flow structures
/// such as if, loops, parallel, abort, ... to form the corresponding
/// graphs for these complex structures.
type ProgramGraph =
    { Entry: Node
      Exit: Node
      Graph: Graph }
    override this.ToString() = this.Graph.ToString()


/// Map a memory location to a source text position and graph node wherein this name is used.
type Mem2Nodes = Dictionary<AccessLabel, ResizeArray<range * Node>>


/// The intermediate context is built during program graph creation
/// and subsequently consumed by the causality analysis.
type IntermediateContext =
    {
        lut: TypeCheckContext
        pgs: Dictionary<QName, ProgramGraph> // Program Graph for a subprogram
        subprogReadNodes: Dictionary<QName, Mem2Nodes> // For a given subprogram, a mapping of memory locations to nodes that read those
        subprogWrittenNodes: Dictionary<QName, Mem2Nodes> // For a given subprogram, a mapping of memory locations to nodes that write those
        tempNameReadByNodes: Mem2Nodes
        tempNameWrittenByNodes: Mem2Nodes
    }
    member this.ReInitNodeDicts () =
        { this with 
            tempNameWrittenByNodes = Dictionary()
            tempNameReadByNodes = Dictionary() }
    static member Empty (lut) =
        { lut = lut
          pgs = Dictionary()
          subprogReadNodes = Dictionary()
          subprogWrittenNodes = Dictionary()
          tempNameWrittenByNodes = Dictionary()
          tempNameReadByNodes = Dictionary() }


[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module MemoryLabel =
    /// Apply f to label regardless of timepoint
    let mapLst f memLab =
        match memLab with
        | Cur m -> f m |> List.map Cur
        | Prev m -> f m |> List.map Prev
        | Next m -> f m |> List.map Next
        | SubProg n -> [SubProg n] // nothing to do for a name