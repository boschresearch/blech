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


/// This type represents integer constants
/// They as integer literals of type AnyInt,
/// or as integer constants of type IntX or NatX
type Integer = 
    { value: bigint }
    
    override this.ToString() =
        string this.value

    static member Zero = 
        { value = 0I }
      
    member this.IsZero = 
        this.value = 0I

    member this.UnaryMinus =
        { value = Arithmetic.UnaryMinusInteger this }

    static member Arithmetic (operator: Arithmetic) (left: Integer) (right: Integer) : Integer =
        { value = operator.BinaryInteger left right }
      

/// This type represents integer constants
/// They appear as bits literals of type AnyBit,
/// or as bits constants of type bits8, bits16, bits32, bits64
and Bits = 
    { value: bigint 
      size: int        // size: 8, 16, 32, 64, needed for operators
      repr: string option }

    override this.ToString() =
        match this.repr with
        | Some s -> s
        | None -> string this.value

    static member Zero size = 
        { value = 0I; size = size; repr = None }
    
    member this.IsZero = 
        this.value = 0I

    member this.UnaryMinus: Bits =
        printfn "Bits size: %s" <| string this.size
        let value = Arithmetic.UnaryMinusBits this
        { value = value // numeric wrap-around
          size = this.size
          repr = None } // there is no representation, like '- 0xFF' 

    static member FromInteger (value: bigint) (size: int) : Bits =
        let wrapAround = pown 2I size
        let wrapped = if value < 0I then wrapAround + value else value
        // printfn "Required Size: %s Bits form integer: %s -> %s" (string size) (string value) (string wrapped)
        { value = wrapped
          size = size 
          repr = None }


    static member Arithmetic (operator: Arithmetic) (left: Bits) (right: Bits) : Bits =
        let size = if left.size > right.size then left.size else right.size
        let value = operator.BinaryBits size left right
        { value = value 
          size = size
          repr = None }


    static member Relational op left right : bool = 
        op left.value right.value


/// This type represents float constants
/// They appear as float literals of type AnyFloat,
/// or as float constants of type float32 or float64
and Float = 
    { value: float
      size: int  // 32 or 64, needed for operators
      repr: string option }

    member this.IsOverflow  = 
        this.value = System.Double.PositiveInfinity

    //static member mkOverflow (repr: string option) =
    //    { value = System.Double.PositiveInfinity; size = 0; repr = repr }

    override this.ToString() =
        match this.repr, this.size with
        | Some s, _ -> s
        | None, 32 -> string <| float32 this.value
        | None, 64 -> string this.value
        | None, _ -> failwith "Not a valid size"

    static member Zero size = 
        { value = 0.0; size = size; repr = None }

    member this.IsZero =
        this.value = 0.0

    member this.UnaryMinus : Float =
        let negVal = Arithmetic.UnaryMinusFloat this
        match this.repr with
        | Some r -> {value = negVal; size = this.size; repr = Some ("-" + r)}
        | None -> {value = negVal; size = this.size; repr = None}

    static member CanRepresent (i: bigint) =
        abs i <= MAX_FLOAT64_INT

    static member Relational op left right = 
        op left.value right.value
    
    static member Arithmetic (op: Arithmetic) left right =
        let size = if left.size > right.size then left.size else right.size
        let value = op.BinaryFloat left right
        {value = value; size = size; repr = None}


and Arithmetic =
    | Unm
    | Add
    | Sub
    | Mul
    | Div
    | Mod

    static member UnaryMinusBits(bits: Bits) = 
        let bv = bits.value
        match bits.size with
        | 8 -> 0uy - uint8 bv |> uint32 |> bigint
        | 16 -> 0us - uint16 bv |> uint32 |> bigint
        | 32 -> 0u - uint32 bv |> bigint
        | 64 -> 0UL - uint64 bv |> bigint
        | _ -> failwith "Not a valid size"

    member this.BinaryBits (size: int) (left: Bits) (right: Bits) : bigint =
        let lv = left.value
        let rv = right.value
        match this, size with
        | Add, 8 -> uint8 lv + uint8 rv |> uint32 |> bigint 
        | Add, 16 -> uint16 lv + uint16 rv |> uint32 |> bigint 
        | Add, 32 -> uint32 lv + uint32 rv |> bigint 
        | Add, 64 -> uint64 lv + uint64 rv |> bigint 
        | Sub, 8 -> uint8 lv - uint8 rv |> uint32 |> bigint 
        | Sub, 16 -> uint16 lv - uint16 rv |> uint32 |> bigint 
        | Sub, 32 -> uint32 lv - uint32 rv |> bigint 
        | Sub, 64 -> uint64 lv - uint64 rv |> bigint 
        | Mul, 8 -> uint8 lv * uint8 rv |> uint32 |> bigint 
        | Mul, 16 -> uint16 lv * uint16 rv |> uint32 |> bigint 
        | Mul, 32 -> uint32 lv * uint32 rv |> bigint 
        | Mul, 64 -> uint64 lv * uint64 rv |> bigint 
        | Div, 8 -> uint8 lv / uint8 rv |> uint32 |> bigint 
        | Div, 16 -> uint16 lv / uint16 rv |> uint32 |> bigint 
        | Div, 32 -> uint32 lv / uint32 rv |> bigint 
        | Div, 64 -> uint64 lv / uint64 rv |> bigint 
        | Mod, 8 -> uint8 lv % uint8 rv |> uint32 |> bigint 
        | Mod, 16 -> uint16 lv % uint16 rv |> uint32 |> bigint 
        | Mod, 32 -> uint32 lv % uint32 rv |> bigint 
        | Mod, 64 -> uint64 lv % uint64 rv |> bigint 
        | Unm, _ -> failwith "Unm is not a binary bits operator"
        | _, _ -> failwith "Not a valid size"

    static member UnaryMinusInteger (i: Integer): bigint = 
        - i.value

    member this.BinaryInteger (left: Integer) (right: Integer): bigint =
        let lv = left.value
        let rv = right.value
        match this with
        | Add -> lv + rv
        | Sub -> lv - rv
        | Mul -> lv * rv
        | Div -> lv / rv
        | Mod -> lv % rv
        | Unm -> failwith "Unm is not a binary integer operator"
        
    static member UnaryMinusFloat (cfloat: Float) : float =
        match cfloat.size with
        | 32 -> - float32 cfloat.value |> float 
        | 64 -> - cfloat.value
        | _ -> failwith "Not a valid size"

    member this.BinaryFloat (left: Float) (right: Float): float =
        let size = if left.size > right.size then left.size else right.size
        let lv = left.value
        let rv = right.value
        match this, size with
        | Add, 32 -> float32 lv + float32 rv |> float
        | Add, 64 -> float lv + float rv
        | Sub, 32 -> float32 lv - float32 rv |> float
        | Sub, 64 -> float lv - float rv
        | Mul, 32 -> float32 lv * float32 rv |> float
        | Mul, 64 -> float lv * float rv
        | Div, 32 -> float32 lv / float32 rv |> float
        | Div, 64 -> float lv / float rv
        | Mod, _ -> failwith "Modulo '%' is not allowed for floats"
        | Unm, _ -> failwith "Unm is not a binary float operator"
        | _, _ -> failwith "Not a valid size"    


and Logical =
    | Not
    | And 
    | Or

and Relational = 
    | Eq
    | Lt
    | Le

and Bitwise =  
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
    
    member this.BinaryBits (left: Bits) (right: Bits): bigint =
        let size = if left.size > right.size then left.size else right.size
        let lv = left.value
        let rv = right.value
        match this, size with
        | Bor, 8 -> uint8 lv ||| uint8 rv |> uint32 |> bigint
        | Band, 8-> uint8 lv &&& uint8 rv |> uint32 |> bigint
        | Bxor, 8 -> uint8 lv ^^^ uint8 rv |> uint32 |> bigint
        | _ -> failwith "Not a bitwise binary operator"

    member this.ShiftBits (bits: Bits) (amount: int32) =
        let size = bits.size
        match this, size with
        | Shl, 8 -> uint8 bits.value <<< amount |> uint32 |> bigint
        | Shr, 8 -> uint8 bits.value >>> amount |> uint32 |> bigint
        | _ -> failwith "Not a shift operator"

    member this.AdvancedShiftBits (bits: Bits) (amount: int32) : bigint = 
        let size = bits.size
        let b = bits.value
        match this, size with
        | Ashr, 8 -> (int8 b) >>> amount |> uint8 |> uint32 |> bigint 
        // TODO: lookup rotate algorithms in Hacker's Delight, fjg. 6.2.20
        | Rotl, _ -> failwith "Not yet implemented"
        | Rotr, _ -> failwith "Not yet implemented"
        | _ -> failwith "Not an advanced shift operator"
    
