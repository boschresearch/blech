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

//[<RequireQualifiedAccess>]
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


type Arithmetic =
    | Unm
    | Add
    | Sub
    | Mul
    | Div
    | Mod

    member this.binaryBits (size: int) (left: bigint) (right: bigint) =
        match this, size with
        | Add, 8 -> uint8 left + uint8 right |> uint32 |> bigint 
        | Add, 16 -> uint16 left + uint16 right |> uint32 |> bigint 
        | Add, 32 -> uint32 left + uint32 right |> bigint 
        | Add, 64 -> uint64 left + uint64 right |> bigint 
        | Sub, 8 -> uint8 left - uint8 right |> uint32 |> bigint 
        | Sub, 16 -> uint16 left - uint16 right |> uint32 |> bigint 
        | Sub, 32 -> uint32 left - uint32 right |> bigint 
        | Sub, 64 -> uint64 left - uint64 right |> bigint 
        | Mul, 8 -> uint8 left * uint8 right |> uint32 |> bigint 
        | Mul, 16 -> uint16 left * uint16 right |> uint32 |> bigint 
        | Mul, 32 -> uint32 left * uint32 right |> bigint 
        | Mul, 64 -> uint64 left * uint64 right |> bigint 
        | Div, 8 -> uint8 left / uint8 right |> uint32 |> bigint 
        | Div, 16 -> uint16 left / uint16 right |> uint32 |> bigint 
        | Div, 32 -> uint32 left / uint32 right |> bigint 
        | Div, 64 -> uint64 left / uint64 right |> bigint 
        | Mod, 8 -> uint8 left % uint8 right |> uint32 |> bigint 
        | Mod, 16 -> uint16 left % uint16 right |> uint32 |> bigint 
        | Mod, 32 -> uint32 left % uint32 right |> bigint 
        | Mod, 64 -> uint64 left % uint64 right |> bigint 
        | Unm, _ -> failwith "Unm is not a binary bits operator"
        | _, _ -> failwith "Not a valid size"

    member this.binaryInt (left: bigint) (right: bigint): bigint =
        match this with
        | Add -> left + right
        | Sub -> left - right
        | Mul -> left * right
        | Div -> left / right
        | Mod -> left % right
        | Unm -> failwith "Unm is not a binary integer operator"
        
    member this.binaryFloat (left: float) (right: float): float =
        match this with
        | Add -> left + right
        | Sub -> left - right
        | Mul -> left * right
        | Div -> left / right
        | Mod -> failwith "Modulo '%' is not allowed for floats"
        | Unm -> failwith "Unm is not a binary float operator"
            

type Logical =
    | Not
    | And 
    | Or

type Relational = 
    | Eq
    | Lt
    | Le

type Bitwise =  
    | Bnot
    | Band
    | Bor
    | Bxor
    | Shl
    | Shr
    | Ashr
    | Rotl
    | Rotr

    member this.BnotBits8 (bits: uint8) =
        match this with
        | Bnot -> ~~~ bits
        | _ -> failwith "Not the bitwise not operator"
    
    member this.BnotBits16 (bits: uint16) =
        match this with
        | Bnot -> ~~~ bits
        | _ -> failwith "Not the bitwise not operator"
    
    member this.BinaryBits8 (left: uint8) (right: uint8) =
        match this with
        | Bor -> left ||| right
        | Band -> left &&& right
        | Bxor -> left ^^^ right
        | _ -> failwith "Not a bitwise binary operator"

    member this.ShiftBits8 (bits: uint8) (amount: int32) =
        match this with
        | Shl -> bits <<< amount
        | Shr -> bits >>> amount
        | _ -> failwith "Not a shift operator"

    member this.AdvancedShiftBits8 (bits: uint8) (amount: int32) = 
        match this with
        | Ashr -> (int8 bits) >>> amount |> uint8
        // TODO: lookup rotate algorithms in Hacker's Delight, fjg. 6.2.20
        | Rotl -> failwith "Not yet implemented"
        | Rotr -> failwith "Not yet implemented"
        | _ -> failwith "Not an advanced shift operator"
    

/// Carries the parsed value and the orginal representation
type Float = 
    { value: float
      repr: string option }

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

    member this.IsZero =
        this.value = 0.0

    member this.UnaryMinus : Float =
        let negVal = - this.value
        match this.repr with
        | Some r -> {value = negVal; repr = Some ("-" + r)}
        | None -> {value = negVal; repr = None}

    static member CanRepresent (i: bigint) =
        abs i <= MAX_FLOAT64_INT

    static member Relational op left right = 
        op left.value right.value
    
    static member Arithmetic op left right =
        {value = op left.value right.value; repr = None}
