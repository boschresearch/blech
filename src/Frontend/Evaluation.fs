module Blech.Frontend.Evaluation

open Constants
open CommonTypes


type Constant = 
    | Zero

    static member FloatZero (size: CommonTypes.FloatType) = 
        match size with
        | Float32 -> Float.Zero32
        | Float64 -> Float.Zero64

    static member BitsZero (size: CommonTypes.BitsType) = 
        match size with
        | Bits8 -> Bits.Zero8
        | Bits16 -> Bits.Zero16
        | Bits32 -> Bits.Zero32
        | Bits64 -> Bits.Zero64

type Arithmetic =
    | Unm
    | Add
    | Sub
    | Mul
    | Div
    | Mod

    member this.UnaryMinusBits (bits: Bits) = 
        match this, bits with
        | Unm, B8 v -> B8 <| 0uy - v
        | Unm, B16 v -> B16 <| 0us - v        
        | Unm, B32 v -> B32 <| 0u - v 
        | Unm, B64 v -> B64 <| 0UL - v
        | Unm, _ -> failwith "Unary Minus for BAny not allowed"
        | _ -> failwith "Not the unary minus operator "

    member this.BinaryBits (left: Bits) (right: Bits) : Bits =
        let l = left.PromoteTo right
        let r = right.PromoteTo left
        match this, left, right with
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

    member this.RelationalBits (left: Bits) (right: Bits) : bool = 
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
    


