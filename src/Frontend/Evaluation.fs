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

/// Unchecked operators are needed for Bits
type Unchecked = 
    static member (+) (l: uint8, r: uint8) = l + r
    static member (-) (l: uint8, r: uint8) = l + r
    static member (*) (l: uint8, r: uint8) = l + r
    
    static member (+) (l: uint16, r: uint16) = l + r
    static member (-) (l: uint16, r: uint16) = l + r
    static member (*) (l: uint16, r: uint16) = l + r

    static member (+) (l: uint32, r: uint32) = l + r
    static member (-) (l: uint32, r: uint32) = l + r
    static member (*) (l: uint32, r: uint32) = l + r

    static member (+) (l: uint64, r: uint64) = l + r
    static member (-) (l: uint64, r: uint64) = l + r
    static member (*) (l: uint64, r: uint64) = l + r

// Checked operators are needed for Int and Nat
// Warning unary minus is not checked, maybe a bug in FSharp?
open Microsoft.FSharp.Core.Operators.Checked

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
    
    // Operator Unm, unary '-'
    
    static member Unm (i: Int) : Int =
        match i with
        | I8 v -> I8 (0y - v)
        | I16 v -> I16 (0s - v)        
        | I32 v -> I32 (0 - v) 
        | I64 v -> I64 (0L - v)
        | IAny (v, Some s) -> IAny (0I - v, Some <| "-" + s) 
        | IAny (v, None) -> IAny (0I - v, None) 

    static member Unm (bits: Bits) : Bits = 
        match bits with
        | B8 v -> B8 <| Unchecked.(-) (0uy, v)
        | B16 v -> B16 <| Unchecked.(-) (0us, v)        
        | B32 v -> B32 <| Unchecked.(-) (0u, v) 
        | B64 v -> B64 <| Unchecked.(-) (0uL, v)
        | BAny _ -> failwith "Unary Minus for BAny not allowed"
    
    static member Unm (nat: Nat) : Nat = 
        match nat with
        | N8 v -> N8 <| 0uy - v
        | N16 v -> N16 <| 0us - v        
        | N32 v -> N32 <| 0u - v 
        | N64 v -> N64 <| 0uL - v

    static member Unm (f : Float) : Float =
        match f with
        | F32 v -> F32 -v 
        | F64 v -> F64 -v
        | FAny (v, Some s) -> FAny (-v, Some <| "-" + s) 
        | FAny (v, None) -> FAny (-v, None) 

    // Operator Add, '+'

    static member Add (left: Int, right: Int) : Int =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | I8 lv, I8 rv -> I8 <| lv + rv 
        | I16 lv, I16 rv -> I16 <| lv + rv 
        | I32 lv, I32 rv -> I32 <| lv + rv 
        | I64 lv, I64 rv -> I64 <| lv + rv 
        | _, _ -> failwith "Add not allowed for IAny or Ints of different size"

    static member Add (left: Bits, right: Bits) : Bits =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | B8 lv, B8 rv -> B8 <| Unchecked.(+) (lv, rv) 
        | B16 lv, B16 rv -> B16 <| Unchecked.(+) (lv, rv) 
        | B32 lv, B32 rv -> B32 <| Unchecked.(+) (lv, rv) 
        | B64 lv, B64 rv -> B64 <| Unchecked.(+) (lv, rv) 
        | _, _ -> failwith "Add not allowed for BAny or Bits of different size"

    static member Add (left: Nat, right: Nat) : Nat =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | N8 lv, N8 rv -> N8 <| lv + rv 
        | N16 lv, N16 rv -> N16 <| lv + rv 
        | N32 lv, N32 rv -> N32 <| lv + rv 
        | N64 lv, N64 rv -> N64 <| lv + rv 
        | _, _ -> failwith "Add not allowed for Nats of different size"

    static member Add (left: Float, right: Float) : Float =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | F32 lv, F32 rv -> F32 <| lv + rv
        | F64 lv, F64 rv -> F64 <| lv + rv
        | _, _ -> failwith "Add not allowed for FAny or Floats of different size"
        
    // Operator Sub, '-'

    static member Sub (left: Int, right: Int) : Int =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | I8 lv, I8 rv -> I8 <| lv - rv 
        | I16 lv, I16 rv -> I16 <| lv - rv 
        | I32 lv, I32 rv -> I32 <| lv - rv 
        | I64 lv, I64 rv -> I64 <| lv - rv 
        | _, _ -> failwith "Sub not allowed for IAny or Int of different size"

    static member Sub (left: Bits, right: Bits) : Bits =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | B8 lv, B8 rv -> B8 <| Unchecked.(-) (lv, rv)
        | B16 lv, B16 rv -> B16 <| Unchecked.(-) (lv, rv) 
        | B32 lv, B32 rv -> B32 <| Unchecked.(-) (lv, rv) 
        | B64 lv, B64 rv -> B64 <| Unchecked.(-) (lv, rv) 
        | _, _ -> failwith "Sub not allowed for BAny or Bits of different size"

    static member Sub (left: Nat, right: Nat) : Nat =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | N8 lv, N8 rv -> N8 <| lv - rv 
        | N16 lv, N16 rv -> N16 <| lv - rv 
        | N32 lv, N32 rv -> N32 <| lv - rv 
        | N64 lv, N64 rv -> N64 <| lv - rv 
        | _, _ -> failwith "Sub not allowed for Nats of different size"

    static member Sub (left: Float, right: Float) : Float =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | F32 lv, F32 rv -> F32 <| lv - rv
        | F64 lv, F64 rv -> F64 <| lv - rv
        | _, _ -> failwith "Sub not allowed for FAny or Floats of different size"
        
    // Operator Mul, '*'

    static member Mul (left: Int, right: Int) : Int =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | I8 lv, I8 rv -> I8 <| lv * rv 
        | I16 lv, I16 rv -> I16 <| lv * rv 
        | I32 lv, I32 rv -> I32 <| lv * rv 
        | I64 lv, I64 rv -> I64 <| lv * rv 
        | _, _ -> failwith "Mul not allowed for IAny or Ints of different size"

    static member Mul (left: Bits, right: Bits) : Bits =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | B8 lv, B8 rv -> B8 <| Unchecked.(*) (lv, rv)
        | B16 lv, B16 rv -> B16 <| Unchecked.(*) (lv, rv)
        | B32 lv, B32 rv -> B32 <| Unchecked.(*) (lv, rv) 
        | B64 lv, B64 rv -> B64 <| Unchecked.(*) (lv, rv) 
        | _, _ -> failwith "Mul not allowed for BAny or Bits of different size"

    static member Mul (left: Nat, right: Nat) : Nat =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | N8 lv, N8 rv -> N8 <| lv * rv 
        | N16 lv, N16 rv -> N16 <| lv * rv 
        | N32 lv, N32 rv -> N32 <| lv * rv 
        | N64 lv, N64 rv -> N64 <| lv * rv 
        | _, _ -> failwith "Mul not allowed for Nats of different size"

    static member Mul (left: Float, right: Float) : Float =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | F32 lv, F32 rv -> F32 <| lv * rv
        | F64 lv, F64 rv -> F64 <| lv * rv
        | _, _ -> failwith "Mul not allowed for FAny or Floats of different size"
        
    // Operator Div, '/'

    static member Div (left: Int, right: Int) : Int =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | I8 lv, I8 rv -> I8 <| lv / rv 
        | I16 lv, I16 rv -> I16 <| lv / rv 
        | I32 lv, I32 rv -> I32 <| lv / rv 
        | I64 lv, I64 rv -> I64 <| lv / rv 
        //| IAny (lv, _), IAny (rv, _) -> IAny (lv / rv, None)
        | _, _ -> failwith "Div not allowed for IAny or Ints of different size"

    static member Div (left: Bits, right: Bits) : Bits =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | B8 lv, B8 rv -> B8 <| lv / rv 
        | B16 lv, B16 rv -> B16 <| lv / rv 
        | B32 lv, B32 rv -> B32 <| lv / rv 
        | B64 lv, B64 rv -> B64 <| lv / rv 
        | _, _ -> failwith "Div not allowed for BAny or Bits of different size"

    static member Div (left: Nat, right: Nat) : Nat =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | N8 lv, N8 rv -> N8 <| lv / rv 
        | N16 lv, N16 rv -> N16 <| lv / rv 
        | N32 lv, N32 rv -> N32 <| lv / rv 
        | N64 lv, N64 rv -> N64 <| lv / rv 
        | _, _ -> failwith "Div not allowed for Nats of different size"

    static member Div (left: Float, right: Float) : Float =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | F32 lv, F32 rv -> F32 <| lv / rv
        | F64 lv, F64 rv -> F64 <| lv / rv
        | _, _ -> failwith "Div not allowed for FAny or Floats of different size"
    
    // Operator Mod, '%', not allowed for Floats

    static member Mod (left: Int, right: Int) : Int =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | I8 lv, I8 rv -> I8 <| lv % rv 
        | I16 lv, I16 rv -> I16 <| lv % rv 
        | I32 lv, I32 rv -> I32 <| lv % rv 
        | I64 lv, I64 rv -> I64 <| lv % rv 
        | _, _ -> failwith "Mod not allowed for IAny or Ints of different size"

    static member Mod (left: Bits, right: Bits) : Bits =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | B8 lv, B8 rv -> B8 <| lv % rv 
        | B16 lv, B16 rv -> B16 <| lv % rv 
        | B32 lv, B32 rv -> B32 <| lv % rv 
        | B64 lv, B64 rv -> B64 <| lv % rv 
        | _, _ -> failwith "Mod not allowed for BAny or Bits of different size"

    static member Mod (left: Nat, right: Nat) : Nat =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | N8 lv, N8 rv -> N8 <| lv % rv 
        | N16 lv, N16 rv -> N16 <| lv % rv 
        | N32 lv, N32 rv -> N32 <| lv % rv 
        | N64 lv, N64 rv -> N64 <| lv % rv 
        | _, _ -> failwith "Mod not allowed for Nats of different size"

// TODO: This is not needed, delete it, fjg. 14.02.20
//type Logical =

//    static member Not (b: bool) : bool = 
//        not b 

//    static member And (left: bool, right: bool) : bool = 
//        left && right

//    static member Or (left: bool, right: bool) : bool = 
//        left || right

type Relational = 
        
    static member Eq (left: Int, right: Int): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match l, r with
        | I8 lv, I8 rv -> lv = rv 
        | I16 lv, I16 rv -> lv = rv 
        | I32 lv, I32 rv -> lv = rv 
        | I64 lv, I64 rv -> lv = rv
        | IAny (lv, _), IAny (rv, _) -> lv = rv
        | _, _ -> failwith "Invalid Eq for Int"  
    
    static member Eq (left: Nat, right: Nat): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match l, r with
        | N8 lv, N8 rv -> lv = rv 
        | N16 lv, N16 rv -> lv = rv 
        | N32 lv, N32 rv -> lv = rv 
        | N64 lv, N64 rv -> lv = rv
        | _, _ -> failwith "Invalid Eq for Nat"  
        
    static member Eq (left: Bits, right: Bits): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match l, r with
        | B8 lv, B8 rv -> lv = rv 
        | B16 lv, B16 rv -> lv = rv 
        | B32 lv, B32 rv -> lv = rv 
        | B64 lv, B64 rv -> lv = rv
        | BAny (lv, _), BAny (rv, _) -> lv = rv
        | _, _ -> failwith "Invalid Eq for Bits"  

    static member Eq (left: Float, right: Float): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match l, r with
        | F32 lv, F32 rv -> lv = rv
        | F64 lv, F64 rv -> lv = rv
        | FAny (lv, _), FAny (rv, _) -> lv = rv
        | _, _ -> failwith "Invalid Eq for Float"  


    static member Lt (left: Int, right: Int): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match l, r with
        | I8 lv, I8 rv -> lv < rv 
        | I16 lv, I16 rv -> lv < rv 
        | I32 lv, I32 rv -> lv < rv 
        | I64 lv, I64 rv -> lv < rv
        | IAny (lv, _), IAny (rv, _) -> lv < rv
        | _, _ -> failwith "Invalid Lt for Int"  

    static member Lt (left: Nat, right: Nat): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match l, r with
        | N8 lv, N8 rv -> lv < rv 
        | N16 lv, N16 rv -> lv < rv 
        | N32 lv, N32 rv -> lv < rv 
        | N64 lv, N64 rv -> lv < rv
        | _, _ -> failwith "Invalid Lt for Nat"  
    
    static member Lt (left: Bits, right: Bits): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match l, r with
        | B8 lv, B8 rv -> lv < rv 
        | B16 lv, B16 rv -> lv < rv 
        | B32 lv, B32 rv -> lv < rv 
        | B64 lv, B64 rv -> lv < rv
        | BAny (lv, _), BAny (rv, _) -> lv < rv
        | _, _ -> failwith "Invalid Lt for Bits"  

    static member Lt (left: Float, right: Float): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match l, r with
        | F32 lv, F32 rv -> lv < rv
        | F64 lv, F64 rv -> lv < rv
        | FAny (lv, _), FAny (rv, _) -> lv < rv
        | _, _ -> failwith "Invalid Lt for Float"  

    static member Le (left: Int, right: Int): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match l, r with
        | I8 lv, I8 rv -> lv <= rv 
        | I16 lv, I16 rv -> lv <= rv 
        | I32 lv, I32 rv -> lv <= rv 
        | I64 lv, I64 rv -> lv <= rv
        | IAny (lv, _), IAny (rv, _) -> lv <= rv
        | _, _ -> failwith "Invalid Le for Int"  

    static member Le (left: Nat, right: Nat): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match l, r with
        | N8 lv, N8 rv -> lv <= rv 
        | N16 lv, N16 rv -> lv <= rv 
        | N32 lv, N32 rv -> lv <= rv 
        | N64 lv, N64 rv -> lv <= rv
        | _, _ -> failwith "Invalid Le for Nat"  

    static member Le (left: Bits, right: Bits): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match l, r with
        | B8 lv, B8 rv -> lv <= rv 
        | B16 lv, B16 rv -> lv <= rv 
        | B32 lv, B32 rv -> lv <= rv 
        | B64 lv, B64 rv -> lv <= rv
        | BAny (lv, _), BAny (rv, _) -> lv <= rv
        | _, _ -> failwith "Invalid Le for Bits"  

    static member Le (left: Float, right: Float): bool =
        let l = left.PromoteTo right
        let r = right.PromoteTo left    
        match l, r with
        | F32 lv, F32 rv -> lv <= rv
        | F64 lv, F64 rv -> lv <= rv
        | FAny (lv, _), FAny (rv, _) -> lv <= rv
        | _, _ -> failwith "Invalid Le for Float"  



and Bitwise =  

    static member Bnot (bits: Bits) =
        match bits with
        | B8 b -> B8 ~~~b        
        | B16 b -> B16 ~~~b        
        | B32 b -> B32 ~~~b        
        | B64 b -> B64 ~~~b        
        | _ -> failwith "Bnot on AnyBits not allowed"
    
    static member Band (left: Bits, right: Bits) =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | B8 lv, B8 rv -> B8 <| (lv &&& rv) 
        | B16 lv, B16 rv -> B16 <| (lv &&& rv) 
        | B32 lv, B32 rv -> B32 <| (lv &&& rv)
        | B64 lv, B64 rv -> B64 <| (lv &&& rv) 
        | _ -> failwith "No BAnd on BAny allowed"
    
    static member Bor (left: Bits, right: Bits) =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | B8 lv, B8 rv -> B8 <| (lv ||| rv) 
        | B16 lv, B16 rv -> B16 <| (lv ||| rv) 
        | B32 lv, B32 rv -> B32 <| (lv ||| rv)
        | B64 lv, B64 rv -> B64 <| (lv ||| rv) 
        | _ -> failwith "No BOr on BAny allowed"
    
    static member Bxor (left: Bits, right: Bits) =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match l, r with
        | B8 lv, B8 rv -> B8 <| (lv ^^^ rv) 
        | B16 lv, B16 rv -> B16 <| (lv ^^^ rv) 
        | B32 lv, B32 rv -> B32 <| (lv ^^^ rv)
        | B64 lv, B64 rv -> B64 <| (lv ^^^ rv) 
        | _ -> failwith "No BXor on BAny allowed"
    
    static member Shl (bits: Bits, amount: int32) : Bits =
        match bits with
        | B8 b -> B8 (b <<< amount)
        | B16 b -> B16 (b <<< amount)
        | B32 b -> B32 (b <<< amount)
        | B64 b -> B64 (b <<< amount)
        | BAny _ -> failwith "No Shl on BAny allowed"

    static member Shr (bits: Bits, amount: int32) : Bits =
        match bits with
        | B8 b -> B8 (b >>> amount)
        | B16 b -> B16 (b >>> amount)
        | B32 b -> B32 (b >>> amount)
        | B64 b -> B64 (b >>> amount)
        | BAny _ -> failwith "No Shl on BAny allowed"

    static member Sshr (bits: Bits, amount: int32) : Bits =
        match bits with
        | B8 b -> int8 b >>> amount |> uint8 |> B8
        | B16 b -> int16 b >>> amount |> uint16 |> B16
        | B32 b -> int32 b >>> amount |> uint32 |> B32
        | B64 b -> int64 b >>> amount |> uint64 |> B64
        | BAny _ -> failwith "No signed shift right '+>>' on BAny allowed"

    static member Rotl (bits: Bits, amount: int32) : Bits =
        match bits with
        | B8 b -> b <<< amount ||| b >>> 8 - amount |> B8 
        | B16 b -> b <<< amount ||| b >>> 16 - amount |> B16 
        | B32 b -> b <<< amount ||| b >>> 32 - amount |> B32 
        | B64 b -> b <<< amount ||| b >>> 64 - amount |> B64 
        | BAny _ -> failwith "No rotate left '<<>' on BAny allowed"

    static member Rotr (bits: Bits, amount: int32) : Bits =
        match bits with
        | B8 b -> b >>> amount ||| b <<< 8 - amount |> B8 
        | B16 b -> b >>> amount ||| b <<< 16 - amount |> B16 
        | B32 b -> b >>> amount ||| b <<< 32 - amount |> B32 
        | B64 b -> b >>> amount ||| b <<< 64 - amount |> B64 
        | BAny _ -> failwith "No rotate right '<>>' on BAny allowed"

