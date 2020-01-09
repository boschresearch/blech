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

open System.Collections.Generic

open Blech.Common.PPrint

open Blech.Frontend
open Blech.Frontend.CommonTypes
open Blech.Frontend.BlechTypes

open Blech.Intermediate


type Action = Blech.Intermediate.Action

type TranslationContext = {
    tcc: TypeCheckContext
    pgs: Dictionary<QName, ProgramGraph>
    bgs: Dictionary<QName, BlockGraph.T>
    cliContext: Blech.Common.Arguments.BlechCOptions
}



/// Represents a translated Blech activity or function
// A list of these is built by the code generator
type Compilation =
    { name: QName
      iface: Iface
      varsToPrev: QName list
      localPcs: ParamDecl list
      signature: Doc
      implementation: Doc 
      doc: Doc option}
    static member Empty =
        { name = mkAuxQNameFrom ""
          iface = Iface.Empty
          varsToPrev = []
          localPcs = []
          signature = empty
          implementation = empty
          doc = None }

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Compilation =    
    open Iface

    /// Takes interface of the callee, mangles names,
    /// integrates it into the interface of calling compilation unit
    /// returns mangled interface
    let internal includeIface pcDoc caller (callee: Compilation) =
        let merge (p: ParamDecl) =
            // merge who to call and parameter name
            let pcPref = pcDoc |> render None
            let prefix = pcPref :: callee.name.toPrefix @ p.name.prefix
            let basicId = p.name.basicId
            QName.CreateAuxiliary prefix basicId

        let pref parameters =
            parameters
            |> List.map (fun p -> {p with ParamDecl.name = merge p})

        let prefIface =
            {
                inputs = pref callee.iface.inputs
                outputs = pref callee.iface.outputs
                retvar = callee.iface.retvar
                pcs = pref callee.iface.pcs
                locals = pref callee.iface.locals
            }
        let mergedIface = includeIfaceInIface (!caller).iface prefIface
        caller := {!caller with iface = mergedIface}
        prefIface
