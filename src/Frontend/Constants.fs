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

/// This module collects types which are used accross different places in the frontend and that
/// the programmer usually wants to "open". Separating CommonTypes from the latter BlechTypes
/// allows to perform this open, without opening the whole typed AST (which possibly clashes
/// with the untyped AST.)

module Blech.Frontend.Constants

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
let MAX_FLOAT32_INT = pown 2I 24 
let MAX_FLOAT64_INT = pown 2I 53

/// Converts a bigint to an uint8 assuming it fits
let private bigint2uint8 v =
    if v < 0I then uint8 <| pown 2I 8 + v
    else uint8 v

/// Converts a bigint to an uint16 assuming it fits
let private bigint2uint16 v =
    if v < 0I then uint16 <| pown 2I 16 + v
    else uint16 v

/// Converts a bigint to an uint32 assuming it fits
let private bigint2uint32 v =
    if v < 0I then uint32 <| pown 2I 32 + v
    else uint32 v

/// Converts a bigint to an uint64 assuming it fits
let private bigint2uint64 v =
    if v < 0I then uint64 <| pown 2I 64 + v
    else uint64 v
    
/// This type represents constants for array indexes.
/// Bits, Nat, Int can be used for an array index.
type Size = uint64
let SizeZero : Size = 0uL
let SizeOne : Size = 1uL

/// This type represents float constants
/// They appear as float literals of type AnyFloat,
/// or as float constants of type float32 or float64
type Float = 
    | F32 of float32
    | F64 of float
    | FAny of float * string option 
    
    override this.ToString() =
        match this with
        | F32 v -> string v
        | F64 v -> string v
        | FAny (_, Some s)-> s
        | FAny (v, None) -> string v

    member this.IsAny =
        match this with
        | FAny _ -> true
        | _ -> false

    member this.IsZero =
        match this with
        | F32 v -> v = 0.0f
        | F64 v -> v = 0.0
        | FAny (v, _) -> v = 0.0
    
    member this.PromoteTo (other: Float) : Float = 
        match this, other with
        | F32 v, F64 _ -> F64 <| float v
        | FAny (v, _), F32 _ -> F32 <| float32 v  // typecheck ensures fitting values 
        | FAny (v, _), F64 _ -> F64 v             // typecheck ensures fitting values
        | _ -> this  // no promotion necessary


    static member Zero32: Float = F32 0.0f

    static member Zero64: Float = F64 0.0

    // Todo: Get rid of this, fjg. 10.02.20
    static member CanRepresent (i: bigint) =
        abs i <= MAX_FLOAT64_INT

/// This type represents sizes.
/// They appear as array size and array index
/// The type checker ensures the limitation to the word size of the target machine.

/// This type represents natural constants
/// They appear constants of type Nx
type Nat = 
    | N8 of uint8
    | N16 of uint16
    | N32 of uint32
    | N64 of uint64

    override this.ToString() =
        match this with
        | N8 v -> string v
        | N16 v -> string v
        | N32 v -> string v
        | N64 v -> string v

    static member Zero8 = N8 0uy
    static member Zero16 = N16 0us
    static member Zero32 = N32 0u
    static member Zero64 = N64 0uL
    
    member this.IsZero = 
        match this with
        | N8 v -> v = 0uy
        | N16 v -> v = 0us
        | N32 v -> v = 0u
        | N64 v -> v = 0uL

    member this.IsAny = false // Todo: Do we really need this? fjg. 11.02.20

    /// This extracts the Size from a Nat constant.
    member this.GetSize : Size =
        match this with
        | N8 v -> uint64 v
        | N16 v -> uint64 v
        | N32 v -> uint64 v 
        | N64 v -> uint64 v

    member this.PromoteTo (other: Nat) : Nat = 
        match this, other with
        | N8 v, N16 _ -> N16 <| uint16 v
        | N8 v, N32 _ -> N32 <| uint32 v
        | N8 v, N64 _ -> N64 <| uint64 v
        | N16 v, N32 _ -> N32 <| uint32 v
        | N16 v, N64 _ -> N64 <| uint64 v
        | N32 v, N64 _ -> N64 <| uint64 v
        | _ -> this


/// This type represents integer constants
/// They appear as bits literals of type AnyBit,
/// or as bits constants of type bits8, bits16, bits32, bits64
type Bits = 
    | B8 of uint8
    | B16 of uint16
    | B32 of uint32
    | B64 of uint64
    | BAny of bigint * string // No operations allowed for BAny constants, therefore string not optional

    override this.ToString() =
        match this with
        | B8 v -> string v
        | B16 v -> string v
        | B32 v -> string v
        | B64 v -> string v
        | BAny (_, s) -> s 


    static member Zero8 = B8 0uy
    static member Zero16 = B16 0us
    static member Zero32 = B32 0u
    static member Zero64 = B64 0uL

    member this.IsZero = 
        match this with
        | B8 v -> v = 0uy
        | B16 v -> v = 0us
        | B32 v -> v = 0u
        | B64 v -> v = 0uL
        | BAny (v, _) -> v = 0I 

    /// This extracts the Size from an Bits constant.
    /// The typechecker must guarantee, that no overflow occurs
    member this.GetSize : Size =
        try 
            match this with
            | B8 v -> uint64 v 
            | B16 v -> uint64 v
            | B32 v -> uint64 v
            | B64 v -> uint64 v 
            | BAny (v, _) -> uint64 v
        with
        | :? System.OverflowException ->
            failwith "Called on unchecked size constant"

    member this.PromoteTo (nat: Nat) =
        // typechecker ensures that this can be represented as Bits
        match this, nat with
        | BAny (v, _), N8 _ -> N8 <| uint8 v
        | BAny (v, _), N16 _ -> N16 <| uint16 v
        | BAny (v, _), N32 _ -> N32 <| uint32 v
        | BAny (v, _), N64 _ -> N64 <| uint64 v
        | _ -> failwith "Only BAny can be promoted to Nat"

    member this.PromoteTo (other: Bits) : Bits = 
        match this, other with
        | B8 v, B16 _ -> B16 <| uint16 v
        | B8 v, B32 _ -> B32 <| uint32 v
        | B8 v, B64 _ -> B64 <| uint64 v
        | B16 v, B32 _ -> B32 <| uint32 v
        | B16 v, B64 _ -> B64 <| uint64 v
        | B32 v, B64 _ -> B64 <| uint64 v
        | BAny (v, _), B8 _ -> B8 <| uint8 v   // typecheck ensures fitting values 
        | BAny (v, _), B16 _ -> B16 <| uint16 v  // typecheck ensures fitting values 
        | BAny (v, _), B32 _ -> B32 <| uint32 v  // typecheck ensures fitting values 
        | BAny (v, _), B64 _ -> B64 <| uint64 v  // typecheck ensures fitting values
        | _ -> this  // no promotion necessary


/// This type represents integer constants
/// They appear as integer literals of type IAny,
/// or as integer constants of type Ix
type Int = 
    | I8 of int8
    | I16 of int16
    | I32 of int32
    | I64 of int64
    | IAny of bigint * string option
    
    override this.ToString() =
        match this with
        | I8 v -> string v
        | I16 v -> string v
        | I32 v -> string v
        | I64 v -> string v
        | IAny (v, None) -> string v
        | IAny (_, Some s) -> s

    static member Zero8 = I8 0y
    static member Zero16 = I16 0s
    static member Zero32 = I32 0
    static member Zero64 = I64 0L
      
    member this.IsZero = 
        match this with
        | I8 v -> v = 0y
        | I16 v -> v = 0s
        | I32 v -> v = 0
        | I64 v -> v = 0L
        | IAny (v, _) -> v = 0I
        
    member this.IsAny =
        match this with
        | IAny _ -> true
        | _ -> false
    
    /// This extracts the Size from an Int constant.
    /// The typechecker must guarantee, that no overflow occurs
    member this.GetSize : Size =
        try 
            match this with
            | I8 v -> uint64 v
            | I16 v -> uint64 v
            | I32 v -> uint64 v
            | I64 v -> uint64 v
            | IAny (v, _) -> uint64 v 
        with
        | :? System.OverflowException ->
            failwith "Called on unchecked size constant"  //

    member this.PromoteTo (nat: Nat) =
        // typechecker ensures that this can be represented as Bits
        match this, nat with
        | IAny (v, _), N8 _ -> N8 <| uint8 v
        | IAny (v, _), N16 _ -> N16 <| uint16 v
        | IAny (v, _), N32 _ -> N32 <| uint32 v
        | IAny (v, _), N64 _ -> N64 <| uint64 v
        | _ -> failwith "Only IAny can be promoted to Nat"

    member this.PromoteTo (bits: Bits) : Bits =
        // typechecker ensures that this can be represented as Bits
        // Assume 2s complement conversion for negative values
        match this, bits with
        | IAny (v, _), B8 _ -> B8 <| bigint2uint8 v
        | IAny (v, _), B16 _ -> B16 <| bigint2uint16 v
        | IAny (v, _), B32 _ -> B32 <| bigint2uint32 v
        | IAny (v, _), B64 _ -> B64 <| bigint2uint64 v
        | _ -> failwith "Only IAny can be promoted to Bits"

    member this.PromoteTo (bits: Float) : Float =
        // typechecker ensures that this can be represented as Float
        match this, bits with
        | IAny (v, _), F32 _ -> F32 <| float32 v
        | IAny (v, _), F64 _ -> F64 <| float v
        | _ -> failwith "Only IAny can be promoted to Float"
    
    member this.PromoteTo (int: Int) : Int =
        // typechecker ensures that this can be represented as Bits
        match this, int with
        | I8 v, I16 _ -> I16 <| int16 v
        | I8 v, I32 _ -> I32 <| int32 v
        | I8 v, I64 _ -> I64 <| int64 v
        | I16 v, I32 _ -> I32 <| int32 v
        | I16 v, I64 _ -> I64 <| int64 v
        | I32 v, I64 _ -> I64 <| int64 v
        // typecheck ensures that any values can be represented
        | IAny (v, _), I8 _ -> I8 <| int8 v
        | IAny (v, _), I16 _ -> I16 <| int16 v
        | IAny (v, _), I32 _ -> I32 <| int32 v
        | IAny (v, _), I64 _ -> I64 <| int64 v
        | _ -> this // no promotion necessary 
    
