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

module List =
    let rec unzip4 x =
        match x with
        | [] ->
            [], [], [], []
        | (h1, h2, h3, h4) :: t ->
            let res1, res2, res3, res4 = unzip4 t
            h1::res1, h2::res2, h3::res3, h4::res4


module Pair = 
    open System.Collections.Generic
    let order (compare1: IComparer<'T1>, compare2: IComparer<'T2>) =
        { new IComparer<'T1 * 'T2> with 
             member __.Compare((a1,a2),(aa1,aa2)) =
                  let res1 = compare1.Compare (a1, aa1)
                  if res1 <> 0 then res1 else compare2.Compare (a2, aa2) }


module Map = 
    let collectWithOverride (maps: Map<'a, 'b> list) : Map<'a, 'b> =
        let mapfolder acc key value = Map.add key value acc
        let listfolder acc map = Map.fold mapfolder acc map
        List.fold listfolder Map.empty maps


    let collect (maps: Map<'a, 'b> list) : Map<'a, 'b> =
        let mapfolder acc key value =
            if Map.containsKey key acc then 
                failwith <| sprintf "Key: %A already bound" key
            else 
                Map.add key value acc
        let listfolder acc map = Map.fold mapfolder acc map
        List.fold listfolder Map.empty maps

// --------------------------------------------------------------------------
//  String
// --------------------------------------------------------------------------

[<RequireQualifiedAccess>]
module String =

    /// converts a string to a list of chars
    let explode (str : string) = str.ToCharArray() |> List.ofArray

    /// converts a list of chars to a string
    let implode chars = System.String (List.toArray chars)

    let order = LanguagePrimitives.FastGenericComparer<String>

    /// restricts the length of a string for String.make
    let MaxLength = Int32.MaxValue

    /// returns a fresh string of length n, filled with the character c. 
    let fill n (c: char) = "".PadLeft(n,c)


// --------------------------------------------------------------------------
//  Result
// --------------------------------------------------------------------------
[<RequireQualifiedAccess>]
module Result =

    let isError (result: Result<'ok, 'err>) : bool =
        match result with
        | Ok _ -> false
        | Error _ -> true
    
    let isOk (result: Result<'ok, 'err>) : bool =
        match result with
        | Ok _ -> true
        | Error _ -> false

    let getOk (result: Result<'ok, 'err>) : 'ok = 
        match result with 
        | Error err -> failwithf "Could not get Ok item from Result as it contains an error: %A" err 
        | Ok ok -> ok
        
    let getError (result: Result<'ok, 'err>) : 'err = 
        match result with 
        | Error err -> err 
        | Ok ok -> failwithf "Could not get Error from Result: %A" ok


type ResultBuilder() =
    member __.Return(x) = Ok x

    member __.ReturnFrom(m: Result<_, _>) = m

    member __.Bind(m, f) = Result.bind f m
    
    member __.Zero() = None

    member __.Combine(m, f) = Result.bind f m

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
