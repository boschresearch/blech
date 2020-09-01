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
module Blech.Frontend.CommonTypes

open Blech.Common
open Constants

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
        QName.Create moduleName [] id (IdLabel.Static) // Program identifiers are always top-level and do not need a path
         
    member qn.IsAuxiliary = 
        qn.label = Auxiliary

    member qn.IsStatic =
        qn.label = Static

    member qn.IsDynamic = 
        qn.label = Dynamic

    // TODO: This is currently only used for acitivity states, which does not take imports into account,
    // therefore it does not take qn.moduleName into account. Change this with code generation for imports, fjg 26.01.19
    // unused
    //member qn.toPrefix = 
    //    qn.prefix @ [qn.basicId]

    member this.ToUnderscoreString() =
        List.foldBack (fun n s -> n + "_" + s) this.prefix this.basicId
   
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

let mkPrefixIndexedNameFrom s =
    let cur = !auxVarIndex
    auxVarIndex := 1 + !auxVarIndex
    sprintf "%s_%s" (string cur) s

    
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

/// Behaviour is required for operators
type Behaviour =
    | Safe
    | Unsafe
    | Throwing
    override this.ToString() = 
        match this with
        | Safe -> ""
        | Unsafe -> "!"
        | Throwing -> "?"


// Checked casts are needed for conversions and narrowing
open Microsoft.FSharp.Core.Operators.Checked


/// This enum reflects the possible sizes of an IntExpr.
/// The numbers are chosen such that type A is supertype of B if A >= B.
/// In that case the cast from B into A is implicit and safe.
type IntType = 
    | Int8 | Int16 | Int32 | Int64 // order of tags matters for comparison!

    override this.ToString() = "int" + string this.GetSize
    
    member this.GetSize =
        match this with
        | Int8 -> 8
        | Int16 -> 16
        | Int32 -> 32
        | Int64 -> 64
        
    /// Checks if IntType can represent an AnyInt value
    static member CanRepresent (anyInt: Int) =
        Int64.CanRepresent anyInt    

    member this.CanRepresent (anyInt: Int) =
        match this, anyInt with
        | Int8, IAny (value, _) -> MIN_INT8 <= value && value <= MAX_INT8
        | Int16, IAny (value, _) -> MIN_INT16 <= value && value <= MAX_INT16
        | Int32, IAny (value, _) -> MIN_INT32 <= value && value <= MAX_INT32
        | Int64, IAny (value, _) -> MIN_INT64 <= value && value <= MAX_INT64
        | _ -> failwith "This is only used for IAny values"

    member this.AllowsConversion (anyBits: Bits) =
        match this, anyBits with
        | Int8, BAny (value, _) -> MIN_BITS8 <= value && value <= MAX_INT8
        | Int16, BAny (value, _) -> MIN_BITS16  <= value && value <= MAX_INT16
        | Int32, BAny (value, _) -> MIN_BITS32 <= value && value <= MAX_INT32
        | Int64, BAny (value, _) -> MIN_BITS64 <= value && value <= MAX_INT64
        | _ -> failwith "This is only used for BAny values"

    member this.Convert (anyBits: Bits) =
        try 
            match this, anyBits with
            | Int8, BAny (value, _) -> I8 <| sbyte value 
            | Int16, BAny (value, _) -> I16 <| int16 value 
            | Int32, BAny (value, _) -> I32 <| int32 value
            | Int64, BAny (value, _) -> I64 <| int64 value
            | _ -> failwith "This is only used for BAny values"
        with
        | :? System.OverflowException -> 
            failwith "Called with unchecked BAny value"

    member this.AllowsNarrowing (value: Int) = 
        match this, value with
        | Int8, I16 i -> int16 MIN_INT8 <= i && i <= int16 MAX_INT8
        | Int8, I32 i -> int32 MIN_INT8 <= i && i <= int32 MAX_INT8
        | Int8, I64 i -> int64 MIN_INT8 <= i && i <= int64 MAX_INT8
        | Int16, I32 i -> int32 MIN_INT16 <= i && i <= int32 MAX_INT16
        | Int16, I64 i -> int64 MIN_INT16 <= i && i <= int64 MAX_INT16
        | Int32, I64 i -> int64 MIN_INT32 <= i && i <= int64 MAX_INT32
        | _ -> 
            failwith "called for wrong narrowing"

    member this.AllowsNarrowing (bits: Bits) = 
        match this, bits with
        | Int8, B8 b -> b <= uint8 MAX_INT8
        | Int8, B16 b -> b <= uint16 MAX_INT8
        | Int8, B32 b -> b <= uint32 MAX_INT8
        | Int8, B64 b -> b <= uint64 MAX_INT8
        | Int16, B16 b -> b <= uint16 MAX_INT16
        | Int16, B32 b -> b <= uint32 MAX_INT16
        | Int16, B64 b -> b <= uint64 MAX_INT16
        | Int32, B32 b -> b <= uint32 MAX_INT32
        | Int32, B64 b -> b <= uint64 MAX_INT32
        | Int64, B64 b -> b <= uint64 MAX_INT64
        | _ -> 
            failwith "called for wrong narrowing"

    member this.AllowsNarrowing (nat: Nat) = 
        match this, nat with
        | Int8, N8 n -> n <= uint8 MAX_INT8
        | Int8, N16 n -> n <= uint16 MAX_INT8
        | Int8, N32 n -> n <= uint32 MAX_INT8
        | Int8, N64 n -> n <= uint64 MAX_INT8
        | Int16, N16 n -> n <= uint16 MAX_INT16
        | Int16, N32 n -> n <= uint32 MAX_INT16
        | Int16, N64 n -> n <= uint64 MAX_INT16
        | Int32, N32 n -> n <= uint32 MAX_INT32
        | Int32, N64 n -> n <= uint64 MAX_INT32
        | Int64, N64 n -> n <= uint64 MAX_INT64
        | _ -> 
            failwith "called for wrong narrowing"

    member this.AllowsNarrowing (value: Float) = 
        // A non-zero fractional part is discarded
        match this, value with
        | Int8, F32 f -> float32 MIN_INT8 <= f && f <= float32 MAX_INT8
        | Int8, F64 f -> float MIN_INT8 <= f && f <= float MAX_INT8
        | Int16, F32 f -> float32 MIN_INT16 <= f && f <= float32 MAX_INT16
        | Int16, F64 f -> float MIN_INT16 <= f && f <= float MAX_INT16
        | Int32, F32 f -> float32 MIN_INT32 <= f && f <=  float32 MAX_INT32
        | Int32, F64 f -> float MIN_INT32 <= f && f <= float MAX_INT32 
        | Int64, F32 f -> float32 MIN_INT64 <= f && f <=  float32 MAX_INT32
        | Int64, F64 f -> float MIN_INT64 <= f && f <=  float MAX_INT64
        | _ -> 
            failwith "called for wrong narrowing"

    static member RequiredType (value: Int) =
        match value with
        | IAny (value, _) ->
            if MIN_INT8 <= value && value <= MAX_INT8 then Int8
            elif MIN_INT16 <= value && value <= MAX_INT16 then Int16
            elif MIN_INT32 <= value && value <= MAX_INT32 then Int32
            elif MIN_INT64 <= value && value <= MAX_INT64 then Int64
            else failwith "IAny value outside any IntX type"
        | _ ->
            failwith "Not an IAny value"

    member this.AdoptAny (any: Int) : Int =
        match this, any with
        | Int8, IAny _ -> any.PromoteTo Int.Zero8
        | Int16, IAny _ -> any.PromoteTo Int.Zero16
        | Int32, IAny _ -> any.PromoteTo Int.Zero32
        | Int64, IAny _ -> any.PromoteTo Int.Zero64
        | _ -> failwith "Adoption of any not allowed"


type NatType = 
    | Nat8 | Nat16 | Nat32 | Nat64 // order of tags matters for comparison!

    override this.ToString() = "nat" + string this.GetSize
    
    member this.GetSize =
        match this with
        | Nat8 -> 8
        | Nat16 -> 16
        | Nat32 -> 32
        | Nat64 -> 64

    /// Checks if a NatType can represent a value of an IntType
    //member this.CanRepresentType (typ: IntType) =
        //match this with
        //| Nat8 -> typ <= Int8
        //| Nat16 -> typ <= Int16
        //| Nat32 -> typ <= Int32
        //| Nat64 -> typ <= Int64
    
    /// Checks if NatType can represent an AnyBits value
    static member CanRepresent (anyBits: Bits) =
        Nat64.CanRepresent anyBits    

    /// Checks if NatType can represent an AnyInt value
    static member CanRepresent (anyInt: Int) =
        Nat64.CanRepresent anyInt
    
    member this.CanRepresent (anyBits: Bits) =
        match this, anyBits with
        | Nat8, BAny (value, _) -> MIN_NAT8 <= value && value <= MAX_NAT8
        | Nat16, BAny (value, _) -> MIN_NAT16 <= value && value <= MAX_NAT16
        | Nat32, BAny (value, _) -> MIN_NAT32 <= value && value <= MAX_NAT32
        | Nat64, BAny (value, _) -> MIN_NAT64 <= value && value <= MAX_NAT64
        | _ -> failwith "This is only used for BAny values"
   
    member this.CanRepresent (anyInt: Int) =
        match this, anyInt with
        | Nat8, IAny (value, _) -> MIN_NAT8 <= value && value <= MAX_NAT8
        | Nat16, IAny (value, _) -> MIN_NAT16 <= value && value <= MAX_NAT16
        | Nat32, IAny (value, _) -> MIN_NAT32<= value && value <= MAX_NAT32
        | Nat64, IAny (value, _) -> MIN_NAT64 <= value && value <= MAX_NAT64
        | _ -> failwith "This is only used for IAny values"

    
    static member RequiredType (anyInt: Int) =
        match anyInt with
        | IAny (value, _) ->
            if MIN_NAT8 <= value && value <= MAX_NAT8 then Nat8
            elif MIN_NAT16 <= value && value <= MAX_NAT16 then Nat16
            elif MIN_NAT32 <= value && value <= MAX_NAT32 then Nat32
            elif MIN_NAT64 <= value && value <= MAX_NAT64 then Nat64
            else failwith "AnyInt value outside any NatX type"
        | _ -> 
            failwith "Not an IAny value"

    static member RequiredType (anyBits: Bits) =
        match anyBits with
        | BAny (value, _) ->
            if MIN_NAT8 <= value && value <= MAX_NAT8 then Nat8
            elif MIN_NAT16 <= value && value <= MAX_NAT16 then Nat16
            elif MIN_NAT32 <= value && value <= MAX_NAT32 then Nat32
            elif MIN_NAT64 <= value && value <= MAX_NAT64 then Nat64
            else failwith "BAny value outside any NatX type"
        | _ -> 
            failwith "Not an BAny value"

    member this.AdoptAny (any: Int) : Nat =
        match this, any with
        | Nat8, IAny _ -> any.PromoteTo Nat.Zero8
        | Nat16, IAny _ -> any.PromoteTo Nat.Zero16
        | Nat32, IAny _ -> any.PromoteTo Nat.Zero32
        | Nat64, IAny _ -> any.PromoteTo Nat.Zero64
        | _ -> failwith "Adoption of any not allowed"

    
    member this.AdoptAny (any: Bits) : Nat =
        match this, any with
        | Nat8, BAny _ -> any.PromoteTo Nat.Zero8
        | Nat16, BAny _ -> any.PromoteTo Nat.Zero16
        | Nat32, BAny _ -> any.PromoteTo Nat.Zero32
        | Nat64, BAny _ -> any.PromoteTo Nat.Zero64
        | _ -> failwith "Adoption of any not allowed"

    member this.AllowsNarrowing (value: Nat) = 
        match this, value with
        | Nat8, N16 n -> n <= uint16 MAX_NAT8
        | Nat8, N32 n -> n <= uint32 MAX_NAT8
        | Nat8, N64 n -> n <= uint64 MAX_NAT8
        | Nat16, N32 n -> n <= uint32 MAX_NAT16
        | Nat16, N64 n -> n <= uint64 MAX_NAT16
        | Nat32, N64 n -> n <= uint64 MAX_NAT32
        | _ -> 
            failwith "called for wrong narrowing"
           
    member this.AllowsNarrowing (bits: Bits) = 
        match this, bits with
        | Nat8, B16 b -> b <= uint16 MAX_NAT8
        | Nat8, B32 b -> b <= uint32 MAX_NAT8
        | Nat8, B64 b -> b <= uint64 MAX_NAT8
        | Nat16, B32 b -> b <= uint32 MAX_NAT16
        | Nat16, B64 b -> b <= uint64 MAX_NAT16
        | Nat32, B64 b -> b <= uint64 MAX_NAT32
        | _ -> 
            failwith "called for wrong narrowing"

    member this.AllowsNarrowing (value: Int) = 
        match this, value with
        | Nat8, I8 i -> int8 MIN_NAT8 <= i
        | Nat8, I16 i -> int16 MIN_NAT8 <= i && i <= int16 MAX_NAT8
        | Nat8, I32 i -> int32 MIN_NAT8 <= i && i <= int32 MAX_NAT8
        | Nat8, I64 i -> int64 MIN_NAT8 <= i && i <= int64 MAX_NAT8

        | Nat16, I8 i -> int8 MIN_NAT16 <= i
        | Nat16, I16 i -> int16 MIN_NAT16 <= i
        | Nat16, I32 i -> int32 MIN_NAT16 <= i && i <= int32 MAX_NAT16
        | Nat16, I64 i -> int64 MIN_NAT16 <= i && i <= int64 MAX_NAT16
        
        | Nat32, I8 i -> int8 MIN_NAT32 <= i
        | Nat32, I16 i -> int16 MIN_NAT32 <= i
        | Nat32, I32 i -> int32 MIN_NAT32 <= i
        | Nat32, I64 i -> int64 MIN_NAT32 <= i && i <= int64 MAX_NAT32
        
        | Nat64, I8 i -> int8 MIN_NAT64 <= i
        | Nat64, I16 i -> int16 MIN_NAT64 <= i
        | Nat64, I32 i -> int32 MIN_NAT64 <= i
        | Nat64, I64 i -> int64 MIN_NAT64 <= i
        
        | _ -> 
            failwith "called for wrong narrowing"

    member this.AllowsNarrowing (value: Float) = 
        // A non-zero fractional part is discarded
        match this, value with
        | Nat8, F32 f -> float32 MIN_NAT8 <= f && f <= float32 MAX_NAT8
        | Nat8, F64 f -> float MIN_NAT8 <= f && f <= float MAX_NAT8
        | Nat16, F32 f -> float32 MIN_NAT16 <= f && f <= float32 MAX_NAT16
        | Nat16, F64 f -> float MIN_NAT16 <= f && f <= float MAX_NAT16
        | Nat32, F32 f -> float32 MIN_NAT32 <= f && f <=  float32 MAX_NAT32
        | Nat32, F64 f -> float MIN_NAT32 <= f && f <= float MAX_NAT32 
        | Nat64, F32 f -> float32 MIN_NAT64 <= f && f <=  float32 MAX_NAT64
        | Nat64, F64 f -> float MIN_NAT64 <= f && f <=  float MAX_NAT64
        | _ -> 
            failwith "called for wrong narrowing"


type BitsType = 
    | Bits8 | Bits16 | Bits32 | Bits64 // order of tags matters for comparison!

    override this.ToString() = "bits" + string this.GetSize
    
    member this.GetSize : int =
        match this with
        | Bits8 -> 8
        | Bits16 -> 16
        | Bits32 -> 32
        | Bits64 -> 64

    /// Checks if BitsType can represent an AnyBits value
    static member CanRepresent (anyBits: Bits) =
        Bits64.CanRepresent anyBits    

    /// Checks if BitsType can represent an AnyInt value
    static member CanRepresent (anyInt: Int) =
        Bits64.CanRepresent anyInt
    
    member this.CanRepresent (anyBits: Bits) =
        match this, anyBits with
        | Bits8, BAny (value, _) -> MIN_BITS8 <= value && value <= MAX_BITS8
        | Bits16, BAny (value, _) -> MIN_BITS16 <= value && value <= MAX_BITS16
        | Bits32, BAny (value, _) -> MIN_BITS32 <= value && value <= MAX_BITS32
        | Bits64, BAny (value, _) -> MIN_BITS64 <= value && value <= MAX_BITS64
        | _ -> failwith "This is only used for BAny values"
    
    member this.CanRepresent (anyInt: Int) = 
        match this, anyInt with
        | Bits8, IAny (value, _) -> MIN_INT8 <= value && value <= MAX_NAT8
        | Bits16, IAny (value, _) -> MIN_INT16 <= value && value <= MAX_NAT16
        | Bits32, IAny (value, _) -> MIN_INT32 <= value && value <= MAX_NAT32
        | Bits64, IAny (value, _) -> MIN_INT64 <= value && value <= MAX_NAT64
        | _ -> failwith "This is only used for IAny values"

    static member RequiredType (anyBits: Bits) =
        match anyBits with
        | BAny (value, _) ->
            if MIN_BITS8 <= value && value <= MAX_BITS8 then Bits8
            elif MIN_BITS16 <= value && value <= MAX_BITS16 then Bits16
            elif MIN_BITS32 <= value && value <= MAX_BITS32 then Bits32
            elif MIN_BITS64 <= value && value <= MAX_BITS64 then Bits64
            else failwith "BAny value outside any BitsX type"
        | _ -> 
            failwith "Not a BAny value"

    static member RequiredType (anyInt: Int) =
        match anyInt with
        | IAny (value, _) ->
            if MIN_INT8 <= value && value <= MAX_NAT8 then Bits8
            elif MIN_INT16 <= value && value <= MAX_NAT16 then Bits16
            elif MIN_INT32 <= value && value <= MAX_NAT32 then Bits32
            elif MIN_INT64 <= value && value <= MAX_NAT64 then Bits32
            else failwith "IAny value outside any BitsX type"
        | _ -> 
            failwith "Not an IAny value"


    member this.AdoptAny (any: Int) : Bits =
        match this, any with
        | Bits8, IAny _ -> any.PromoteTo Bits.Zero8
        | Bits16, IAny _ -> any.PromoteTo Bits.Zero16
        | Bits32, IAny _ -> any.PromoteTo Bits.Zero32
        | Bits64, IAny _ -> any.PromoteTo Bits.Zero64
        | _ -> failwith "Adoption of any not allowed"

    member this.AdoptAny (any: Bits) : Bits =
        match this, any with
        | Bits8, BAny _ -> any.PromoteTo Bits.Zero8
        | Bits16, BAny _ -> any.PromoteTo Bits.Zero16
        | Bits32, BAny _ -> any.PromoteTo Bits.Zero32
        | Bits64, BAny _ -> any.PromoteTo Bits.Zero64
        | _ -> failwith "Adoption of any not allowed"
               
    member this.AllowsNarrowing (bits: Bits) = 
        match this, bits with
        | Bits8, B16 b -> b <= uint16 MAX_BITS8
        | Bits8, B32 b -> b <= uint32 MAX_BITS8
        | Bits8, B64 b -> b <= uint64 MAX_BITS8
        | Bits16, B32 b -> b <= uint32 MAX_BITS16
        | Bits16, B64 b -> b <= uint64 MAX_BITS16
        | Bits32, B64 b -> b <= uint64 MAX_BITS32
        | _ -> 
            failwith "called for wrong narrowing"

    member this.AllowsNarrowing (value:  Nat) = 
        match this, value with
        |  Bits8, N16 n -> n <= uint16 MAX_BITS8
        |  Bits8, N32 n -> n <= uint32 MAX_BITS8
        |  Bits8, N64 n -> n <= uint64 MAX_BITS8
        |  Bits16, N32 n -> n <= uint32 MAX_BITS16
        |  Bits16, N64 n -> n <= uint64 MAX_BITS16
        |  Bits32, N64 n -> n <= uint64 MAX_BITS32
        | _ -> 
            failwith "called for wrong narrowing"
    
    member this.AllowsNarrowing (value: Int) = 
        match this, value with
        | Bits8, I8 i -> sbyte MIN_BITS8 <= i
        | Bits8, I16 i -> int16 MIN_BITS8 <= i && i <= int16 MAX_BITS8
        | Bits8, I32 i -> int32 MIN_BITS8 <= i && i <= int32 MAX_BITS8
        | Bits8, I64 i -> int64 MIN_BITS8 <= i && i <= int64 MAX_BITS8
        | Bits16, I16 i -> int16 MIN_BITS16 <= i
        | Bits16, I32 i -> int32 MIN_BITS16 <= i && i <= int32 MAX_BITS16
        | Bits16, I64 i -> int64 MIN_BITS16 <= i && i <= int64 MAX_BITS16
        | Bits32, I32 i -> int32 MIN_BITS32 <= i
        | Bits32, I64 i -> int64 MIN_BITS32 <= i && i <= int64 MAX_BITS32
        | Bits64, I64 i -> int64 MIN_BITS64 <= i
        | _ -> 
            failwith "called for wrong narrowing"

    member this.AllowsNarrowing (value: Float) = 
        // A non-zero fractional part is discarded
        match this, value with
        | Bits8, F32 f -> float32 MIN_BITS8 <= f && f <= float32 MAX_BITS8
        | Bits8, F64 f -> float MIN_BITS8 <= f && f <= float MAX_BITS8
        | Bits16, F32 f -> float32 MIN_BITS16 <= f && f <= float32 MAX_BITS16
        | Bits16, F64 f -> float MIN_BITS16 <= f && f <= float MAX_BITS16
        | Bits32, F32 f -> float32 MIN_BITS32 <= f && f <=  float32 MAX_BITS32 
        | Bits32, F64 f -> float MIN_BITS32 <= f && f <= float MAX_BITS32 
        | Bits64, F32 f -> float32 MIN_BITS64 <= f && f <=  float32 MAX_BITS64
        | Bits64, F64 f -> float MIN_BITS64 <= f && f <=  float MAX_BITS64
        | _ -> 
            failwith "called for wrong narrowing"

type FloatType = 
    | Float32 | Float64 // order of tags matters for comparison!

    override this.ToString() = "float" + string this.GetSize

    member this.GetSize =
        match this with
        | Float32 -> 32
        | Float64 -> 64

    /// Checks if Float can represent an AnyFloat value
    static member CanRepresent (anyFloat: Float) =
        Float64.CanRepresent anyFloat    
 
    /// Checks if Float can represent an AnyInt value
    static member CanRepresent (anyInt: Int) =
        Float64.CanRepresent anyInt
 
    member this.CanRepresent (value: Int) =
        match this, value with
        | Float32, IAny (v, _) -> MIN_FLOAT32_INT <= v && v <= MAX_FLOAT32_INT
        | Float64, IAny (v, _) -> MIN_FLOAT64_INT <= v && v <= MAX_FLOAT64_INT
        | _, _ -> failwith ("This is only used for IAny values")

    // only used to test possible cast of bits literal: 0x1 as floatX
    member this.AllowsConversion (anyBits: Bits) =
        match this, anyBits with
        | Float32, BAny (v, _) -> MIN_FLOAT32_INT <= v && v <= MAX_FLOAT32_INT
        | Float64, BAny (v, _) -> MIN_FLOAT64_INT <= v && v <= MAX_FLOAT64_INT
        | _, _ -> failwith ("This is only used for BAny values")

    member this.Convert (anyBits: Bits) =
        try 
            match this, anyBits with
            | Float32, BAny (value, _) -> F32 <| float32 value
            | Float64, BAny (value, _) -> F64 <| float value
            | _ -> failwith "This is only used for BAny values"
        with
        | :? System.OverflowException -> 
            failwith "Called with unchecked BAny value"

    member this.AllowsNarrowing (value: Float) = 
            // A non-zero fractional part is discarded
            match this, value with
            | Float32, F64 f -> MIN_FLOAT32 <= f && f <= MAX_FLOAT32
            | _ -> 
                failwith "called for wrong narrowing"

    member this.AllowsNarrowing (bits: Bits) = 
        match this, bits with
        | Float32, B32 b -> b <= uint32 MAX_FLOAT32_INT
        | Float32, B64 b -> b <= uint64 MAX_FLOAT32_INT
        | Float64, B64 b -> b <= uint64 MAX_FLOAT64_INT
        | _ -> 
            failwith "called for wrong narrowing"
        
    member this.AllowsNarrowing (value:  Nat) = 
        match this, value with
        |  Float32, N32 n -> n <= uint32 MAX_FLOAT32_INT
        |  Float32, N64 n -> n <= uint64 MAX_FLOAT32_INT
        |  Float64, N64 n -> n <= uint64 MAX_FLOAT64_INT
        | _ -> 
            failwith "called for wrong narrowing"
        
    member this.AllowsNarrowing (value: Int) = 
        match this, value with
        | Float32, I32 i -> int32 MIN_FLOAT32_INT <= i && i <= int32 MAX_FLOAT32_INT
        | Float32, I64 i -> int64 MIN_FLOAT32_INT <= i && i <= int64 MAX_FLOAT32_INT
        | Float64, I64 i -> int64 MIN_FLOAT64_INT <= i && i <= int64 MAX_FLOAT64_INT
        | _ -> 
            failwith "called for wrong narrowing"
        
    /// Checks if a given float types can represent a AnyFloat value
    member this.CanRepresent (value: Float) =
        match this, value with
        | Float64, FAny (v, _) -> MIN_FLOAT64 <= v && v <= MAX_FLOAT64
        | Float32, FAny (v, _) -> MIN_FLOAT32 <= v && v <= MAX_FLOAT32
        | _, _-> failwith "This is only used for FAny values"    
        
    static member RequiredType (anyFloat: Float) =
        match anyFloat with
        | FAny (v, _) ->
            if MIN_FLOAT32 <= v && v <= MAX_FLOAT32 then Float32 
            elif MIN_FLOAT64 <= v && v <= MAX_FLOAT64 then Float64 
            else failwith "fAny value outside any FloatX type"
        | _ -> 
            failwith "Not an FAny value"

    static member RequiredType (anyInt: Int) =
        match anyInt with
        | IAny (v, _) ->
            if MIN_FLOAT32_INT <= v && v <= MAX_FLOAT32_INT then Float32 
            elif MIN_FLOAT64_INT <= v && v <= MAX_FLOAT64_INT then Float64 
            else failwith "fAny value outside any FloatX type"
        | _ -> 
            failwith "Not an FAny value"
    
    
    member this.AdoptAny (any: Float) : Float =
        match this, any with
        | Float32, FAny _ -> any.PromoteTo Float.Zero32
        | Float64, FAny _ -> any.PromoteTo Float.Zero64
        | _ -> failwith "Adoption of any not allowed"

    member this.AdoptAny (any: Int) : Float =
        match this, any with
        | Float32, IAny _ -> any.PromoteTo Float.Zero32
        | Float64, IAny _ -> any.PromoteTo Float.Zero64
        | _ -> failwith "Adoption of any not allowed"

