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

/// This module collects types which are used accross different places in the frontend and that
/// the programmer usually wants to "open". Separating CommonTypes from the latter BlechTypes
/// allows to perform this open, without opening the whole typed AST (which possibly clashes
/// with the untyped AST.)
module Blech.Frontend.CommonTypes

open Blech.Common

//=========================================================================
// predefined constants TODO: actually, this should be part of blechconf.h
//=========================================================================
let MIN_INT8 = -pown 2I 7
let MAX_INT8 = pown 2I 7 - 1I
let MIN_INT16 = -pown 2I 15
let MAX_INT16 = pown 2I 15 - 1I
let MIN_INT32 = -pown 2I 31
let MAX_INT32 = pown 2I 31 - 1I
let MIN_INT64 = -pown 2I 63
let MAX_INT64 = pown 2I 63 - 1I

let MIN_NAT8 = 0I
let MAX_NAT8 = pown 2I 8 - 1I
let MIN_NAT16 = 0I
let MAX_NAT16 = pown 2I 16 - 1I
let MIN_NAT32 = 0I
let MAX_NAT32 = pown 2I 32 - 1I
let MIN_NAT64 = 0I
let MAX_NAT64 = pown 2I 64 - 1I

let MIN_BITS8 = 0I
let MAX_BITS8 = pown 2I 8 - 1I
let MIN_BITS16 = 0I
let MAX_BITS16 = pown 2I 16 - 1I
let MIN_BITS32 = 0I
let MAX_BITS32 = pown 2I 32 - 1I
let MIN_BITS64 = 0I
let MAX_BITS64 = pown 2I 64 - 1I

let MIN_FLOAT32 = System.Single.MinValue
let MAX_FLOAT32 = System.Single.MaxValue
let MIN_FLOAT64 = System.Double.MinValue
let MAX_FLOAT64 = System.Double.MaxValue

// Names /////////////////////////////////////////////////////////////////

type Identifier = string

type LongIdentifier = Identifier list

let idsToString (ids: LongIdentifier) =
    String.concat "." ids

type IdLabel = 
    | Auxiliary
    | Static
    | Dynamic // TODO: what the hell is a 'dynamic' QName?
              // It seems in fact that this simply discerns the scope in which this name was introduced.
              // The top-level scope being 'static' and any other scope, such as a subprogram, a for-loop header etc... are called dynamic.
              // Meaning that a subprogram-local const has a QName with 'dynamic' label! What is dynamic about it?
              // For now we use this in CPdataAccess to render names correctly. (fg, 04.04.19)

/// qualified names
type QName = 
    {
        moduleName: SearchPath.ModuleName
        prefix: LongIdentifier // TODO: what exactly is the meaning of prefix? 
                               // Is the following invariant true:
                               // prefix is empty <=> QName is on top level <=> IsStatic, or equivalently
                               // prefix is non-empty <=> QName is declared inside a subprogram <=> IsDynamic
                               // ???
                               // How is that for names in structures? OO style programming?
                               // fg, 04.04.19
        basicId: Identifier
        label: IdLabel
    } 

    static member Create moduleName path id label =
        { 
            moduleName = moduleName
            prefix = path
            basicId = id
            label = label
        }

    static member CreateAuxiliary path id =
        QName.Create [] path id (IdLabel.Auxiliary) // Auxiliary identifiers are always local to modules

    /// Creates a QName for program names: tick, init, printState
    static member CreateProgramName moduleName id =
        QName.Create moduleName [] id (IdLabel.Auxiliary) // Program identifiers are always top-level and do not need a path
         
    member qn.IsAuxiliary = 
        qn.label = Auxiliary

    member qn.IsStatic =
        qn.label = Static

    member qn.IsDynamic = 
        qn.label = Dynamic

    // TODO: This is currently only used for acitivity states, which does not take imports into account,
    // therefore it does not take qn.moduleName into account. Change this with code generation for imports, fjg 26.01.19
    member qn.toPrefix = 
        qn.prefix @ [qn.basicId]
   
    override qn.ToString() =
        List.foldBack (fun n s -> n + "." + s) qn.prefix qn.basicId

/// unqualified name
[<CustomEquality; CustomComparison>]
type Name = 
    {
        id : Identifier
        range: Range.range
    }

    static member FromFileOrDirectoryId (identifier: string) =
        { id = identifier
          range = Range.rangeStartup }
        
    member name.Range = name.range
    
    member name.idToString = name.id
    
    override name.ToString() = name.id

    // Todo: Is it really necessary to use the id - a range should uniquely identify the occurence of a name: fjg 25.07.2018
    override name.Equals obj =
        match obj with
        | :? Name as otherName 
            -> name.range.Code = otherName.range.Code
        | _ -> false
    override name.GetHashCode() = name.range.GetHashCode()

    // Names are ordered according to the start of of their source code position 
    interface System.IComparable with
        member name.CompareTo obj =
            match obj with
            | :? Name as otherName ->
                Range.posOrder.Compare (name.range.Start, otherName.range.Start)
            | _ -> 
                invalidArg "obj" "cannot compare values of different types"



/// index of auxiliary variables
let private auxVarIndex = ref 0

/// returns an auxiliary identifier which never clashes with a Blech identifier    
///  blech identifiers do not allow to have digits following the '_'
let private mkAuxIdentifierFrom text : Identifier =
    let cur = !auxVarIndex
    auxVarIndex := 1 + !auxVarIndex
    sprintf "%s_%s" text (string cur) 

let mkAuxQNameFrom s = 
    QName.CreateAuxiliary [] s

let mkIndexedAuxQNameFrom s = 
    QName.CreateAuxiliary [] <| mkAuxIdentifierFrom s

    
/// Strength is required for cobegin blocks
type Strength = 
    | Weak
    | Strong


type Preemption = 
    | Abort
    | Reset
    | Suspend


type Moment =
    | Before
    | After
    | OnNext


/// This enum reflects the possible sizes of an IntExpr.
/// The numbers are chosen such that type A is supertype of B if A >= B.
/// In that case the cast from B into A is implicit and safe.
type IntType = 
    | Int8 | Int16 | Int32 | Int64 // order of tags matters for comparison!

    override this.ToString() = "int" + string(this.GetSize())
    
    member this.GetSize() =
        match this with
        | Int8 -> 8
        | Int16 -> 16
        | Int32 -> 32
        | Int64 -> 64
    static member RequiredType value =
        if MIN_INT8 <= value && value <= MAX_INT8 then Int8
        elif MIN_INT16 <= value && value <= MAX_INT16 then Int16
        elif MIN_INT32 <= value && value <= MAX_INT32 then Int32
        else Int64


type NatType = 
    | Nat8 | Nat16 | Nat32 | Nat64 // order of tags matters for comparison!

    override this.ToString() = "nat" + string(this.GetSize())
    
    member this.GetSize() =
        match this with
        | Nat8 -> 8
        | Nat16 -> 16
        | Nat32 -> 32
        | Nat64 -> 64
    
    static member RequiredType value =
        if MIN_NAT8 <= value && value <= MAX_NAT8 then Nat8
        elif MIN_NAT16 <= value && value <= MAX_NAT16 then Nat16
        elif MIN_NAT32 <= value && value <= MAX_NAT32 then Nat32
        else Nat64


type BitsType = 
    | Bits8 | Bits16 | Bits32 | Bits64 // order of tags matters for comparison!

    override this.ToString() = "bits" + string(this.GetSize())
    
    member this.GetSize() =
        match this with
        | Bits8 -> 8
        | Bits16 -> 16
        | Bits32 -> 32
        | Bits64 -> 64
    
    static member RequiredType value =
        if MIN_BITS8 <= value && value <= MAX_BITS8 then Bits8
        elif MIN_BITS16 <= value && value <= MAX_BITS16 then Bits16
        elif MIN_BITS32 <= value && value <= MAX_BITS32 then Bits32
        else Bits64


/// Carries the parsed value and the orginal representation
type Float = 
    { value: float
      repr: string option}

    member this.IsOverflow  = 
        this.value = System.Double.PositiveInfinity

    static member mkOverflow (repr: string option) =
        { value = System.Double.PositiveInfinity; repr = repr }

    override this.ToString() =
        match this.repr with
        | Some s -> s
        | None -> string this.value

    static member Zero = 
        { value = 0.0; repr = None }

    member this.Negate =
        let negVal = - this.value
        match this.repr with
        | Some r -> {value = negVal; repr = Some ("-" + r)}
        | None -> {value = negVal; repr = None}


type FloatType = 
    | Float32 | Float64 // order of tags matters for comparison!

    override this.ToString() = "float" + string(this.GetSize())

    member this.GetSize() =
        match this with
        | Float32 -> 32
        | Float64 -> 64
        
    static member RequiredType (f : Float) =
        if float MIN_FLOAT32 <= f.value && f.value <= float MAX_FLOAT32 then Float32
        else Float64
    


