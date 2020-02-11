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

module Blech.Backend.Normalisation

open Blech.Frontend.Constants
open Blech.Frontend.CommonTypes
open Blech.Frontend.BlechTypes
open Blech.Frontend.TypeCheckContext
open Blech.Frontend.TyChkExpressions


let rec internal normaliseAssign ctx (r, lhs, rhs) =
    match rhs.rhs with
    | ArrayConst assigments ->
        // if arrayconst contains dynamic values (not compile-time-constants) rewrite into sequence of assignments
        // otherwise let it be and let code generation take care of possibly necessary tmp variables for memcpy
        let makeIdx (i: Size) =
            { rhs = NatConst <| N64 i //IntConst (bigint(i))
              typ = 
                // IntType.RequiredType (bigint(i))
                ValueTypes <| NatType (NatType.RequiredType <| N64 i)
                // |> IntType
                // |> ValueTypes 
              range = r
            }
        let fieldAsAssign i = 
            let (idx, expr) = assigments.[i]
            match lhs.lhs with
            | LhsCur tml ->
                (r, { lhs = LhsCur (ArrayAccess(tml, makeIdx idx)); typ = expr.typ; range = expr.Range}, expr)
            | LhsNext tml ->
                (r, { lhs = LhsNext (ArrayAccess(tml, makeIdx idx)); typ = expr.typ; range = expr.Range}, expr)
            | Wildcard ->
                (r, { lhs = Wildcard; typ = expr.typ; range = expr.Range}, expr)
            |> normaliseAssign ctx // apply recursively, since substructure assignments need to be flattened, too
        [ for i in 0 .. assigments.Length - 1 -> fieldAsAssign i ]
        |> List.concat
    | StructConst assigments ->
        // rewrite individual struct field assignments into 
        // a sequence of assignments
        assigments
        |> List.map (fun (ident, expr) ->
                match lhs.lhs with
                | LhsCur tml ->
                    (r, { lhs = LhsCur (FieldAccess(tml, ident)); typ = expr.typ; range = expr.Range}, expr)
                | LhsNext tml ->
                    (r, { lhs = LhsNext (FieldAccess(tml, ident)); typ = expr.typ; range = expr.Range}, expr)
                | Wildcard ->
                    (r, { lhs = Wildcard; typ = lhs.typ; range = expr.Range}, expr)
                |> normaliseAssign ctx // apply recursively, since substructure assignments need to be flattened, too
            )
            |> List.concat
    | RhsCur tml when isConstVarDecl ctx tml ->
        getInitValueForTml ctx tml |> function
            | Error _ -> failwith "Trying to normalise a tml which is not entirely constant."
            | Ok initVal -> normaliseAssign ctx (r, lhs, initVal)
    | _ ->
        [ Assign(r, lhs, rhs) ]

/// use in activity context only!
let internal normaliseVarDecl ctx (v: VarDecl) =
    normaliseAssign ctx ( v.pos, 
                          { lhs = LhsCur (Loc v.name); typ = v.datatype; range = v.pos}, 
                          v.initValue )