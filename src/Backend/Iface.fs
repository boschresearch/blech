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

namespace Blech.Backend

open Blech.Frontend.BlechTypes

type Iface =
    {
        inputs: ParamDecl list
        outputs: ParamDecl list
        retvar: ParamDecl option
        pcs: ParamDecl list
        locals: ParamDecl list
    }
    with
    static member Empty =
        {inputs = []; outputs = []; retvar = None; pcs = []; locals = []}

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Iface =
    /// Prepends item to items only if it is not already there.
    let private addUniqueParam (item: ParamDecl) (items: ParamDecl list) =
        items 
        |> List.map (fun p -> p.name)
        |> List.contains item.name
        |> function
            | true -> items
            | false -> items @ [item]

    let internal addInputs iface input = {iface with Iface.inputs = addUniqueParam input iface.inputs}

    let internal addOutputs iface output = {iface with Iface.outputs = addUniqueParam output iface.outputs}

    let internal setRetVar iface var = {iface with Iface.retvar = Some var}

    let internal addPcs iface pc = {iface with Iface.pcs = addUniqueParam pc iface.pcs}

    let internal addLocals iface local = {iface with Iface.locals = addUniqueParam local iface.locals}

    let internal includeIfaceInIface i1 i2 =
        {
            inputs = i1.inputs // inputs remain
            outputs = i1.outputs // outputs remain
            retvar = i1.retvar // the return variable remains
            pcs = i1.pcs @ i2.pcs |> List.distinct
            locals = i1.locals @ i2.locals |> List.distinct
        }