namespace Blech.Common

open System

/// Contains a function to convert a floating point value to a string as
/// precisely as possible
[<AutoOpen>]
module MyFloat =
    let floatToString f =
        sprintf "%.16g" f // a doule has 16 significant digits, see https://en.wikibooks.org/wiki/F_Sharp_Programming/Basic_Concepts


//-------------------------------------------------------------------------
// Orders
// This source code is derived from The F# compiler
//   https://github.com/dotnet/fsharp
// Copyright (c) Microsoft Corporation.  All Rights Reserved., licensed under the MIT license,
// cf. 3rd-party-licenses.txt file in the root directory of this source tree.
//------------------------------------------------------------------------

module Order = 
    open System.Collections.Generic

    let orderBy (p : 'T -> 'U) = 
        { new IComparer<'T> with member __.Compare(x,xx) = compare (p x) (p xx) }

    let orderOn p (pxOrder: IComparer<'U>) = 
        { new IComparer<'T> with member __.Compare(x,xx) = pxOrder.Compare (p x, p xx) }

    let toFunction (pxOrder: IComparer<'U>) x y = pxOrder.Compare(x,y)



module Bool = 
    let order = LanguagePrimitives.FastGenericComparer<bool>

module Int32 = 
    let order = LanguagePrimitives.FastGenericComparer<int>

module Int64 = 
    let order = LanguagePrimitives.FastGenericComparer<int64>


module Pair = 
    open System.Collections.Generic
    let order (compare1: IComparer<'T1>, compare2: IComparer<'T2>) =
        { new IComparer<'T1 * 'T2> with 
             member __.Compare((a1,a2),(aa1,aa2)) =
                  let res1 = compare1.Compare (a1, aa1)
                  if res1 <> 0 then res1 else compare2.Compare (a2, aa2) }


// --------------------------------------------------------------------------
//  String
// --------------------------------------------------------------------------

[<RequireQualifiedAccess>]
module String =

    /// converts a string to a list of chars
    let explode (str : string) =
        if str = null
        then raise <| System.ArgumentException ("explode: argument cannot be null")
        else [ for c in str -> c ] 

    /// converts a list of chars to a string
    let implode chars = System.String (List.toArray chars)
    
    /// replace single characters in a string by another string
    let translate f s =
        let rec translateCL cL =
            match cL with
            | [] -> ""
            | c::cL -> (f c)+(translateCL cL)
        translateCL (explode s)

    let order = LanguagePrimitives.FastGenericComparer<String>

    /// restricts the length of a string for String.make
    let MaxLength = Int32.MaxValue

    /// returns a fresh string of length n, filled with the character c. 
    let make n (c: char) = 
        if n < 0 || n > MaxLength then
            Operators.invalidArg "n" (sprintf "Invalid string length: %s" (string n))
        else
            let cs = seq {for i in 1 .. n -> c}
            new System.String(Array.ofSeq cs)


// --------------------------------------------------------------------------
//  Result
// --------------------------------------------------------------------------
[<RequireQualifiedAccess>]
module Result =

    let isError (result: Result<'a, 'x>) : bool =
        match result with
        | Ok _ -> false
        | Error _ -> true
    
    let isOk (result: Result<'a, 'x>) : bool =
        match result with
        | Ok _ -> true
        | Error _ -> false


//-------------------------------------------------------------------------
// Bits, from fsharp compiler
// This source code is derived from The F# compiler
//   https://github.com/dotnet/fsharp
// Copyright (c) Microsoft Corporation.  All Rights Reserved., licensed under the MIT license,
// cf. 3rd-party-licenses.txt file in the root directory of this source tree.
//------------------------------------------------------------------------

module Bits = 
    let b0 n =  (n          &&& 0xFF)  
    let b1 n =  ((n >>> 8)  &&& 0xFF) 
    let b2 n =  ((n >>> 16) &&& 0xFF) 
    let b3 n =  ((n >>> 24) &&& 0xFF) 

    let rec pown32 n = if n = 0 then 0  else (pown32 (n-1) ||| (1  <<<  (n-1)))
    let rec pown64 n = if n = 0 then 0L else (pown64 (n-1) ||| (1L <<< (n-1)))
    let mask32 m n = (pown32 n) <<< m
    let mask64 m n = (pown64 n) <<< m


// --------------------------------------------------------------------------
//  Printing
// --------------------------------------------------------------------------

[<RequireQualifiedAccess>]
module Printf =
    open System.Text
    
    /// Print to a System.Text.StringBuilder and append a newline
    let bprintfn (builder: StringBuilder) (format: Printf.BuilderFormat<'T>) : 'T =
        let k = fun () -> builder.AppendLine () |> ignore
        Printf.kbprintf k builder format
