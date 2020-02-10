module Blech.Frontend.Evaluation

open Constants
open CommonTypes


type Constant = 
    | Zero

    static member FloatZero (size: CommonTypes.FloatType) = 
        match size with
        | Float32 -> Float.Zero32
        | Float64 -> Float.Zero64

type Arithmetic =
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
        
    member this.UnaryMinusFloat (f : Float) : Float =
        match this, f with
        | Unm, F32 v -> F32 -v 
        | Unm, F64 v -> F64 -v
        | Unm, FAny (v, Some s) -> FAny (-v, Some <| "-" + s) 
        | _ -> failwith "Not an unary minus operator"

    member this.BinaryFloat (left: Float) (right: Float): Float =
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
        | _, _, _ -> failwith "Not a valid width combination"    

and Logical =
    | Not
    | And 
    | Or

and Relational = 
    | Eq
    | Lt
    | Le
    member this.RelationalFloat (left: Float) (right: Float): bool =
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
    


