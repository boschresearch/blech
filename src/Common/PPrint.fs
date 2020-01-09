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

// This source code is derived from PPrint
//   https://github.com/polytypic/PPrint
// Copyright (c) 2016 Vesa Karvonen, licensed under the MIT license,
// cf. 3rd-party-licenses.txt file in the root directory of this source tree.

namespace Blech.Common

module PPrint =

    open System.IO

    type Doc =
      | Empty
      | Lazy of Lazy<Doc>
      | Line of Doc
      | Join of lhs: Doc * rhs: Doc
      | Nest of string * Doc
      | Text of string
      | Choice of wide: Doc * narrow: Doc
      | With of (int -> string -> Doc)
      | User of obj

    [<AutoOpen>]
    module Consts =
      let space = Text " "
      let line = Line space
      let linebreak = Line Empty
      let softline = Choice (space, line)
      let softbreak = Choice (Empty, linebreak)

      let inline join3 l d r = Join (l, Join (d, r))

    type Doc with
      static member (<^>)  (l, r) = Join (l, r)
      static member (<+>)  (l, r) = join3 l space     r
      static member (<.>)  (l, r) = join3 l line      r
      static member (</>)  (l, r) = join3 l softline  r
      static member (<..>) (l, r) = join3 l linebreak r
      static member (<//>) (l, r) = join3 l softbreak r

    [<AutoOpen>]
    module Util =
      let inline (^) x = x
      let inline constant x _ = x
      let inline flip f x y = f y x
      let inline force (s: Lazy<_>) = s.Force ()

    [<AutoOpen>]
    module PPrint =
      let delay th = Lazy ^ lazy th ()

      let empty = Empty
      let space = space
      let line = line
      let linebreak = linebreak
      let softline = softline
      let softbreak = softbreak

      let inline column' withCol = With ^ fun col _ -> withCol col
      let inline nesting' withNest = With ^ fun _ prefix -> withNest prefix.Length

      let column withCol = column' withCol
      let nesting withNest = nesting' withNest

      let txt s = Text s
      let user (x: obj) = User x
      let fmt f = Printf.ksprintf Text f
      let chr (c: char) = Text ^ string c

      let (lparen,   rparen)   as lrparen   = (Text "(", Text ")")
      let (langle,   rangle)   as lrangle   = (Text "<", Text ">")
      let (lbrace,   rbrace)   as lrbrace   = (Text "{", Text "}")
      let (lbracket, rbracket) as lrbracket = (Text "[", Text "]")

      let squote = Text "'"
      let lrsquote = (squote, squote)
      let dquote = Text "\""
      let lrdquote = (dquote, dquote)

      let semi      = Text ";"
      let colon     = Text ":"
      let comma     = Text ","
      let dot       = Text "."
      let backslash = Text "\\"
      let equals    = Text "="

      let punctuate sep (ds: seq<Doc>) = seq {
        use ds = ds.GetEnumerator ()
        if ds.MoveNext () then
          let mutable d = ds.Current
          while ds.MoveNext () do
            yield d <^> sep
            d <- ds.Current
          yield d
      }

      let inline spaces n = String.replicate n " "

      let nestBy s d = Nest (s, d)
      let nest n = nestBy ^ spaces n

      let align d = With ^ fun c p -> d |> nest ^ c-p.Length
      let hang i d = align ^ nest i d
      let indent i d = txt ^ spaces i <^> d |> hang i

      let inline width' d f = column' ^ fun l -> d <^> column' ^ fun r -> f ^ r-l
      let width d f = width' d f

      let inline mkFill p t f d =
        width' d ^ fun w -> if p f w then t f else txt ^ spaces ^ f-w

      let fillBreak n d = mkFill (<) (flip nest linebreak) n d
      let fill n d = mkFill (<=) (constant empty) n d

      let rec flatten doc = delay ^ fun () ->
        match doc with
         | Lazy doc -> flatten ^ force doc
         | Join (lhs, rhs) -> Join (flatten lhs, flatten rhs)
         | Nest (txt, doc) -> Nest (txt, flatten doc)
         | Empty | Text _ | User _ -> doc
         | Line wide -> wide
         | Choice (wide, _) -> wide
         | With f -> With <| fun c p -> f c p |> flatten

      let choice wide narrow = Choice (flatten wide, narrow)
      let group doc = choice doc doc

      // flattenWith and groupWith added for placing custom strings at line breaks 
      // this is useful for rendering C macros over several lines using \\

      // prepend separator s to every linefeed
      let rec private flattenWith s doc = delay ^ fun () ->
        let flattenWiths = flattenWith s
        match doc with
         | Lazy doc -> flattenWiths ^ force doc
         | Join (lhs, rhs) -> Join (flattenWiths lhs, flattenWiths rhs)
         | Nest (txt, doc) -> Nest (txt, flattenWiths doc)
         | Empty | Text _ | User _ -> doc
         | Line l -> Join(s, Line l)
         | Choice (wide, narrow) -> Choice(flattenWiths wide, flattenWiths narrow)
         | With f -> With <| fun c p -> f c p |> flattenWiths
      
      /// Rewrites doc such that every potential linebreak has document s
      /// before the line breaks
      let groupWith s doc = flattenWith s doc

      let gnest n = group >> nest n

      let inline joinWith' bop xs =
        match Seq.fold (fun ys x -> x::ys) [] xs with
         | [] -> empty
         | x::xs -> List.fold (flip bop) x xs
      let joinWith bop xs = joinWith' bop xs

      let joinSep sep xs = xs |> joinWith' ^ fun l r -> join3 l sep r

      let hsep    xs = joinWith' (<+>)  xs
      let hcat    xs = joinWith' (<^>)  xs
      let vsep    xs = joinWith' (<.>)  xs
      let vcat    xs = joinWith' (<..>) xs
      let fillSep xs = joinWith' (</>)  xs
      let fillCat xs = joinWith' (<//>) xs

      let sep xs = group ^ vsep xs
      let cat xs = group ^ vcat xs

      let inline enclose' (l, r) d = join3 l d r
      let enclose (l, r) d = enclose' (l, r) d

      let squotes  d = enclose' lrsquote  d
      let dquotes  d = enclose' lrdquote  d
      let parens   d = enclose' lrparen   d
      let angles   d = enclose' lrangle   d
      let braces   d = enclose' lrbrace   d
      let brackets d = enclose' lrbracket d

      type t =
       | Nil
       | Print of text: string * Lazy<t>
       | Linefeed of prefix: string * Lazy<t>
       | Obj of obj: obj * Lazy<t>

      type [<AbstractClass>] Actions () =
        abstract Line: unit -> unit
        abstract Write: string -> unit
        abstract User: obj -> unit
        default t.Line () = t.Write "\n"
        default t.User _ = ()

      let rec output (actions: Actions) doc =
        match force doc with
         | Nil -> ()
         | Print (str, doc) ->
           actions.Write str
           output actions doc
         | Obj (obj, doc) ->
           actions.User obj
           output actions doc
         | Linefeed (prefix, doc) ->
           actions.Line ()
           actions.Write prefix
           output actions doc

      let rec fits maxCols usedCols doc =
        usedCols <= maxCols &&
        match force doc with
         | Nil | Linefeed _ -> true
         | Obj (_, doc) ->
           fits maxCols usedCols doc
         | Print (str, doc) ->
           fits maxCols (usedCols + str.Length) doc

      type Docs =
        | Done
        | Docs of string * Doc * Docs

      let rec layout maxColsOr0 usedCols = function
        | Done -> Nil
        | Docs (prefix, doc, rest) ->
          match doc with
           | Lazy doc ->
             layout maxColsOr0 usedCols ^ Docs (prefix, force doc, rest)
           | Empty ->
             layout maxColsOr0 usedCols rest
           | Join (lhs, rhs) ->
             layout maxColsOr0 usedCols ^
             Docs (prefix, lhs, Docs (prefix, rhs, rest))
           | Nest (txt, doc) ->
             layout maxColsOr0 usedCols ^ Docs (prefix + txt, doc, rest)
           | Text str ->
             Print (str, lazy layout maxColsOr0 (usedCols + str.Length) rest)
           | User obj ->
             Obj (obj, lazy layout maxColsOr0 usedCols rest)
           | Line _ ->
             Linefeed (prefix, lazy layout maxColsOr0 prefix.Length rest)
           | Choice (wide, narrow) ->
             let wide = layout maxColsOr0 usedCols ^ Docs (prefix, wide, rest)
             if maxColsOr0 = 0 || fits maxColsOr0 usedCols ^ lazy wide
             then wide
             else layout maxColsOr0 usedCols ^ Docs (prefix, narrow, rest)
           | With f ->
             layout maxColsOr0 usedCols ^ Docs (prefix, f usedCols prefix, rest)

      let outputWithActions actions maxCols doc =
        let maxColsOr0 =
          match maxCols with
           | None -> 0
           | Some n ->
             if n <= 0 then failwithf "maxCols: %d" n else n
        output actions ^ lazy layout maxColsOr0 0 (Docs ("", doc, Done))

      let inline outputWithFun write maxCols doc =
        outputWithActions
          {new Actions () with
            member t.Write s = write s}
          maxCols
          doc

      let outputToWriter (tw: TextWriter) maxCols doc =
        outputWithFun tw.Write maxCols doc

      let render maxCols doc =
        use tw = new StringWriter ()
        outputToWriter tw maxCols doc
        tw.ToString ()

