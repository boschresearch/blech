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


module Blech.Frontend.Evaluation

open Constants
open CommonTypes

type Constant = 

    static member Zero (size: IntType) : Int =
        match size with
        | Int8 -> Int.Zero8 
        | Int16 -> Int.Zero16 
        | Int32 -> Int.Zero32 
        | Int64 -> Int.Zero64

    static member Zero (size: NatType) : Nat =
        match size with
        | Nat8 -> Nat.Zero8
        | Nat16 -> Nat.Zero16
        | Nat32 -> Nat.Zero32
        | Nat64 -> Nat.Zero64

    static member Zero (size: BitsType) : Bits = 
        match size with
        | Bits8 -> Bits.Zero8
        | Bits16 -> Bits.Zero16
        | Bits32 -> Bits.Zero32
        | Bits64 -> Bits.Zero64
    
    static member Zero (size: FloatType) : Float = 
        match size with
        | Float32 -> Float.Zero32
        | Float64 -> Float.Zero64

    static member MinValue (size: IntType) : Int =
        match size with
        | Int8 -> I8 System.SByte.MinValue 
        | Int16 -> I16 System.Int16.MinValue
        | Int32 -> I32 System.Int32.MinValue
        | Int64 -> I64 System.Int64.MinValue

    static member MinValue (size: NatType) : Nat =
        match size with
        | Nat8 -> Nat.Zero8
        | Nat16 -> Nat.Zero16
        | Nat32 -> Nat.Zero32
        | Nat64 -> Nat.Zero64

    static member MinValue (size: BitsType) : Bits = 
        match size with
        | Bits8 -> Bits.Zero8
        | Bits16 -> Bits.Zero16
        | Bits32 -> Bits.Zero32
        | Bits64 -> Bits.Zero64

    static member MinValue (size: FloatType) : Float = 
        match size with
        | Float32 -> F32 System.Single.MinValue
        | Float64 -> F64 System.Double.MinValue

    static member MaxValue (size: IntType) : Int =
        match size with
        | Int8 -> I8 System.SByte.MaxValue 
        | Int16 -> I16 System.Int16.MaxValue
        | Int32 -> I32 System.Int32.MaxValue
        | Int64 -> I64 System.Int64.MaxValue

    static member MaxValue (size: NatType) : Nat =
        match size with
        | Nat8 -> N8 System.Byte.MaxValue 
        | Nat16 -> N16 System.UInt16.MaxValue
        | Nat32 -> N32 System.UInt32.MaxValue
        | Nat64 -> N64 System.UInt64.MaxValue

    static member MaxValue (size: BitsType) : Bits = 
        match size with
        | Bits8 -> B8 System.Byte.MaxValue 
        | Bits16 -> B16 System.UInt16.MaxValue
        | Bits32 -> B32 System.UInt32.MaxValue
        | Bits64 -> B64 System.UInt64.MaxValue

    static member MaxValue (size: FloatType) : Float = 
        match size with
        | Float32 -> F32 System.Single.MaxValue
        | Float64 -> F64 System.Double.MaxValue


type Arithmetic =
    | Unm
    | Add
    | Sub
    | Mul
    | Div
    | Mod

    member this.Unary (i: Int): Int = 
        match this, i with
        | Unm, I8 v -> I8 -v
        | Unm, I16 v -> I16 -v        
        | Unm, I32 v -> I32 -v 
        | Unm, I64 v -> I64 -v
        | Unm, IAny (v, Some s) -> IAny (-v, Some <| "-" + s) 
        | Unm, IAny (v, None) -> IAny (-v, None) 
        | _ -> failwith "Not the unary minus operator "

    member this.Unary (bits: Bits) : Bits = 
        match this, bits with
        | Unm, B8 v -> B8 <| 0uy - v
        | Unm, B16 v -> B16 <| 0us - v        
        | Unm, B32 v -> B32 <| 0u - v 
        | Unm, B64 v -> B64 <| 0UL - v
        | Unm, BAny _ -> failwith "Unary Minus for BAny not allowed"
        | _ -> failwith "Not the unary minus operator "
    
    member this.Unary (nat: Nat) : Nat = 
        match this, nat with
        | Unm, N8 v -> N8 <| 0uy - v
        | Unm, N16 v -> N16 <| 0us - v        
        | Unm, N32 v -> N32 <| 0u - v 
        | Unm, N64 v -> N64 <| 0UL - v
        | _ -> failwith "Not the unary minus operator "

    member this.UnaryMinus (f : Float) : Float =
        match this, f with
        | Unm, F32 v -> F32 -v 
        | Unm, F64 v -> F64 -v
        | Unm, FAny (v, Some s) -> FAny (-v, Some <| "-" + s) 
        | Unm, FAny (v, None) -> FAny (-v, None) 
        | _ -> failwith "Not an unary minus operator"


    member this.Binary (left: Bits, right: Bits) : Bits =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match this, l, r with
        | Add, B8 lv, B8 rv -> B8 <| lv + rv 
        | Add, B16 lv, B16 rv -> B16 <| lv + rv 
        | Add, B32 lv, B32 rv -> B32 <| lv + rv 
        | Add, B64 lv, B64 rv -> B64 <| lv + rv 
        | Sub, B8 lv, B8 rv -> B8 <| lv - rv 
        | Sub, B16 lv, B16 rv -> B16 <| lv - rv
        | Sub, B32 lv, B32 rv -> B32 <| lv - rv
        | Sub, B64 lv, B64 rv -> B64 <| lv - rv
        | Mul, B8 lv, B8 rv -> B8 <| lv * rv 
        | Mul, B16 lv, B16 rv -> B16 <| lv * rv
        | Mul, B32 lv, B32 rv -> B32 <| lv * rv
        | Mul, B64 lv, B64 rv -> B64 <| lv * rv
        | Div, B8 lv, B8 rv -> B8 <| lv / rv 
        | Div, B16 lv, B16 rv -> B16 <| lv / rv
        | Div, B32 lv, B32 rv -> B32 <| lv / rv
        | Div, B64 lv, B64 rv -> B64 <| lv / rv
        | Mod, B8 lv, B8 rv -> B8 <| lv % rv 
        | Mod, B16 lv, B16 rv -> B16 <| lv % rv
        | Mod, B32 lv, B32 rv -> B32 <| lv % rv
        | Mod, B64 lv, B64 rv -> B64 <| lv % rv
        | Unm, _, _ -> failwith "Unm is not a binary bits operator"
        | _, _, _ -> failwith "Not a valid size"


    member this.Binary (left: Nat, right: Nat) : Nat =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match this, l, r with
        | Add, N8 lv, N8 rv -> N8 <| lv + rv 
        | Add, N16 lv, N16 rv -> N16 <| lv + rv 
        | Add, N32 lv, N32 rv -> N32 <| lv + rv 
        | Add, N64 lv, N64 rv -> N64 <| lv + rv 
        | Sub, N8 lv, N8 rv -> N8 <| lv - rv 
        | Sub, N16 lv, N16 rv -> N16 <| lv - rv
        | Sub, N32 lv, N32 rv -> N32 <| lv - rv
        | Sub, N64 lv, N64 rv -> N64 <| lv - rv
        | Mul, N8 lv, N8 rv -> N8 <| lv * rv 
        | Mul, N16 lv, N16 rv -> N16 <| lv * rv
        | Mul, N32 lv, N32 rv -> N32 <| lv * rv
        | Mul, N64 lv, N64 rv -> N64 <| lv * rv
        | Div, N8 lv, N8 rv -> N8 <| lv / rv 
        | Div, N16 lv, N16 rv -> N16 <| lv / rv
        | Div, N32 lv, N32 rv -> N32 <| lv / rv
        | Div, N64 lv, N64 rv -> N64 <| lv / rv
        | Mod, N8 lv, N8 rv -> N8 <| lv % rv 
        | Mod, N16 lv, N16 rv -> N16 <| lv % rv
        | Mod, N32 lv, N32 rv -> N32 <| lv % rv
        | Mod, N64 lv, N64 rv -> N64 <| lv % rv
        | Unm, _, _ -> failwith "Unm is not a binary Nat operator"
        | _, _, _ -> failwith "Not a valid size"


    member this.Binary (left: Int, right: Int): Int =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match this, l, r with
        | Add, I8 lv, I8 rv -> I8 <| lv + rv
        | Add, I16 lv, I16 rv -> I16 <| lv + rv
        | Add, I32 lv, I32 rv -> I32 <| lv + rv
        | Add, I64 lv, I64 rv -> I64 <| lv + rv
        | Add, IAny (lv, _), IAny (rv, _) -> IAny (lv + rv, None)
        | Sub, I8 lv, I8 rv -> I8 <| lv - rv
        | Sub, I16 lv, I16 rv -> I16 <| lv - rv
        | Sub, I32 lv, I32 rv -> I32 <| lv - rv
        | Sub, I64 lv, I64 rv -> I64 <| lv - rv
        | Sub, IAny (lv, _), IAny (rv, _) -> IAny (lv - rv, None)
        | Mul, I8 lv, I8 rv -> I8 <| lv * rv
        | Mul, I16 lv, I16 rv -> I16 <| lv * rv
        | Mul, I32 lv, I32 rv -> I32 <| lv * rv
        | Mul, I64 lv, I64 rv -> I64 <| lv * rv
        | Mul, IAny (lv, _), IAny (rv, _) -> IAny (lv * rv, None)
        | Div, I8 lv, I8 rv -> I8 <| lv / rv
        | Div, I16 lv, I16 rv -> I16 <| lv / rv
        | Div, I32 lv, I32 rv -> I32 <| lv / rv
        | Div, I64 lv, I64 rv -> I64 <| lv / rv
        | Div, IAny (lv, _), IAny (rv, _) -> IAny (lv / rv, None)
        | Mod, I8 lv, I8 rv -> I8 <| lv % rv
        | Mod, I16 lv, I16 rv -> I16 <| lv % rv
        | Mod, I32 lv, I32 rv -> I32 <| lv % rv
        | Mod, I64 lv, I64 rv -> I64 <| lv % rv
        | Mod, IAny (lv, _), IAny (rv, _) -> IAny (lv % rv, None)
        | Unm, _, _ -> failwith "Unm is not a binary integer operator"
        | _, _, _ -> failwith "Not a valid size combination"


    member this.Binary (left: Float, right: Float): Float =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match this, l , r with
        | Add, F32 lv, F32 rv -> F32 <| lv + rv
        | Add, F64 lv, F64 rv -> F64 <| lv + rv
        | Add, FAny (lv, _), FAny (rv, _) -> FAny (lv + rv, None)
        | Sub, F32 lv, F32 rv -> F32 <| lv - rv
        | Sub, F64 lv, F64 rv -> F64 <| lv - rv
        | Sub, FAny (lv, _), FAny (rv, _) -> FAny (lv - rv, None)
        | Mul, F32 lv, F32 rv -> F32 <| lv * rv
        | Mul, F64 lv, F64 rv -> F64 <| lv * rv
        | Mul, FAny (lv, _), FAny (rv, _) -> FAny (lv * rv, None)
        | Div, F32 lv, F32 rv -> F32 <| lv / rv
        | Div, F64 lv, F64 rv -> F64 <| lv / rv
        | Div, FAny (lv, _), FAny (rv, _) -> FAny (lv / rv, None)
        | Mod, _, _ -> failwith "Modulo '%' is not allowed for floats"
        | Unm, _, _ -> failwith "Unm is not a binary float operator"
        | _, _, _ -> failwith "Not a valid size combination"    

and Logical =
    | Not
    | And 
    | Or

and Relational = 
    | Eq
    | Lt
    | Le

    member this.Relational (left: Float, right: Float): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match this, l, r with
        | Eq, F32 lv, F32 rv -> lv = rv
        | Eq, F64 lv, F64 rv -> lv = rv
        | Eq, FAny (lv, _), FAny (rv, _) -> lv = rv
        | Lt, F32 lv, F32 rv -> lv < rv
        | Lt, F64 lv, F64 rv -> lv < rv
        | Lt, FAny (lv, _), FAny (rv, _) -> lv < rv
        | Le, F32 lv, F32 rv -> lv <= rv
        | Le, F64 lv, F64 rv -> lv <= rv
        | Le, FAny (lv, _), FAny (rv, _) -> lv <= rv
        | _, _, _ -> failwith "Not a valid width combination"  
        
    member this.Relational (left: Int, right: Int) : bool = 
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match this, l , r with
        | Eq, I8 lv, I8 rv -> lv = rv 
        | Eq, I16 lv, I16 rv -> lv = rv 
        | Eq, I32 lv, I32 rv -> lv = rv 
        | Eq, I64 lv, I64 rv -> lv = rv
        | Eq, IAny (lv, _), IAny (rv, _) -> lv = rv
        | Lt, I8 lv, I8 rv -> lv < rv 
        | Lt, I16 lv, I16 rv -> lv < rv 
        | Lt, I32 lv, I32 rv -> lv < rv 
        | Lt, I64 lv, I64 rv -> lv < rv
        | Lt, IAny (lv, _), IAny (rv, _) -> lv < rv
        | Le, I8 lv, I8 rv -> lv <= rv 
        | Le, I16 lv, I16 rv -> lv <= rv 
        | Le, I32 lv, I32 rv -> lv <= rv 
        | Le, I64 lv, I64 rv -> lv <= rv
        | Le, IAny (lv, _), IAny (rv, _) -> lv <= rv
        | _, _, _ -> failwith "Not a valid width combination"

    member this.Relational (left: Bits, right: Bits) : bool = 
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match this, l , r with
        | Eq, B8 lv, B8 rv -> lv = rv 
        | Eq, B16 lv, B16 rv -> lv = rv 
        | Eq, B32 lv, B32 rv -> lv = rv 
        | Eq, B64 lv, B64 rv -> lv = rv
        | Eq, BAny (lv, _), BAny (rv, _) -> lv = rv
        | Lt, B8 lv, B8 rv -> lv < rv 
        | Lt, B16 lv, B16 rv -> lv < rv 
        | Lt, B32 lv, B32 rv -> lv < rv 
        | Lt, B64 lv, B64 rv -> lv < rv
        | Lt, BAny (lv, _), BAny (rv, _) -> lv < rv
        | Le, B8 lv, B8 rv -> lv <= rv 
        | Le, B16 lv, B16 rv -> lv <= rv 
        | Le, B32 lv, B32 rv -> lv <= rv 
        | Le, B64 lv, B64 rv -> lv <= rv
        | Le, BAny (lv, _), BAny (rv, _) -> lv <= rv
        | _, _, _ -> failwith "Not a valid width combination"

    member this.RelationalNat (left: Nat, right: Nat) : bool = 
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match this, l , r with
        | Eq, N8 lv, N8 rv -> lv = rv 
        | Eq, N16 lv, N16 rv -> lv = rv 
        | Eq, N32 lv, N32 rv -> lv = rv 
        | Eq, N64 lv, N64 rv -> lv = rv
        | Lt, N8 lv, N8 rv -> lv < rv 
        | Lt, N16 lv, N16 rv -> lv < rv 
        | Lt, N32 lv, N32 rv -> lv < rv 
        | Lt, N64 lv, N64 rv -> lv < rv
        | Le, N8 lv, N8 rv -> lv <= rv 
        | Le, N16 lv, N16 rv -> lv <= rv 
        | Le, N32 lv, N32 rv -> lv <= rv 
        | Le, N64 lv, N64 rv -> lv <= rv
        | _, _, _ -> failwith "Not a valid width combination"

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
    
    //member this.BinaryBits (left: Bits) (right: Bits): bigint =
    //    let size = if left.size > right.size then left.size else right.size
    //    let lv = left.value
    //    let rv = right.value
    //    match this, size with
    //    | Bor, 8 -> uint8 lv ||| uint8 rv |> uint32 |> bigint
    //    | Band, 8-> uint8 lv &&& uint8 rv |> uint32 |> bigint
    //    | Bxor, 8 -> uint8 lv ^^^ uint8 rv |> uint32 |> bigint
    //    | _ -> failwith "Not a bitwise binary operator"

    //member this.ShiftBits (bits: Bits) (amount: int32) =
    //    let size = bits.size
    //    match this, size with
    //    | Shl, 8 -> uint8 bits.value <<< amount |> uint32 |> bigint
    //    | Shr, 8 -> uint8 bits.value >>> amount |> uint32 |> bigint
    //    | _ -> failwith "Not a shift operator"

    //member this.AdvancedShiftBits (bits: Bits) (amount: int32) : bigint = 
    //    let size = bits.size
    //    let b = bits.value
    //    match this, size with
    //    | Ashr, 8 -> (int8 b) >>> amount |> uint8 |> uint32 |> bigint 
    //    // TODO: lookup rotate algorithms in Hacker's Delight, fjg. 6.2.20
    //    | Rotl, _ -> failwith "Not yet implemented"
    //    | Rotr, _ -> failwith "Not yet implemented"
    //    | _ -> failwith "Not an advanced shift operator"
    


