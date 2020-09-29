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

namespace Blech.Common

module FromPath =
    open System.Text.RegularExpressions

    // Names for capturing groups
    [<Literal>]
    let Pkg = "pkg"
    [<Literal>]
    let Root = "root"
    [<Literal>]
    let Up = "up"
    [<Literal>]
    let Here = "here"
    [<Literal>]
    let Dir = "dir"
    [<Literal>]
    let File = "file"

    [<Literal>]
    let ReservedPkg = "blech"  // reserved name for unnamed packages
    [<Literal>]
    let Id = "^[_a-zA-Z0-9]+$"  // can be used as part of a C identifier for code generation

    // relevant capturing groups are named: (?<name>pattern)
    let package = sprintf "bl:(?<%s>%s)/" Pkg Id
    let rootDir = sprintf "(?<%s>/)" Root
    let upDirs = sprintf "(?<%s>\\.\\./)+" Up
    let hereDir = sprintf "(?<%s>\\./)" Here
    let directory = sprintf "(?<%s>%s)/" Dir Id
    let moduleFile = sprintf "(?<%s>%s)" File Id
    
    // import paths have the following form
    // bl:package/a/b/file  - external package import
    // /a/b/file            - absolute in-package import with '/' under package dir
    // b/file               - relative in-package import from current directory
    // ./b/file             - relative in-package import with ./ indicating current directory
    // ../../b/file         - relative in-package import with ../ up from current directory
    let pathRegex = 
        Regex <| sprintf "^(%s|%s|%s|%s)?(%s)*(%s)$" 
                         package rootDir upDirs hereDir directory moduleFile 
    
    // Move this to Common.Tests
    let test s =
        let m = pathRegex.Match s 
        let ns : string[] = pathRegex.GetGroupNames()
        //printfn "%A" (pathRegex.Matches s)
        for n in ns do
            let g = m.Groups.[n]
            for c in g.Captures do
                printfn "%s: %s" n c.Value

    /// Checks if a directory or file name - without extension - can be used as a Blech identifier
    let isValidFileOrDirectoryName name =
        let isId = (Regex Id).IsMatch
        not (ReservedPkg.Equals name) && isId name

    
    type ModuleName = string list
    type PackageName = string

    type FromPath = 
        { 
            package: string
            dirs: string list
            file: string 
        } 
        member fp.ToModuleName : ModuleName = 
            fp.package :: fp.dirs @ [fp.file]
        member fp.ToPackageName : PackageName =
            fp.package

    // this is preliminary and just to enable recursion over imports in namechecking. TODO: Remove this, fjg. 23.09.20            
    let moduleNameToFromPath moduleName = 
        try 
            { package = List.head moduleName
              dirs = moduleName.[1 .. moduleName.Length-2]
              file = List.last moduleName}
        with
        | _ -> failwith "this should never happen"

    // dead code
    //let isValid path = 
    //    pathRegex.IsMatch path

    let makeFromPath (current: FromPath) path : Result<FromPath, string list> = 
        let m = pathRegex.Match path
        assert m.Success // assert that fromPath is valid
        let pkg = m.Groups.[Pkg].Captures
        let isRoot = m.Groups.[Root].Captures.Count = 1
        let ups = m.Groups.[Up].Captures
        let isHere = m.Groups.[Here].Captures.Count = 1
        let dirs = [ for d in m.Groups.[Dir].Captures do yield d.Value ]
        let file = m.Groups.[File].Captures.Item(0).Value // there is always 1 file
        if pkg.Count = 1 then // external package import
            Ok { package = pkg.Item(0).Value 
                 dirs = dirs
                 file = file } 
        elif isRoot then // absolute in-package import
            Ok { package = current.package 
                 dirs = dirs
                 file = file }
        elif ups.Count > 0 then
            if ups.Count <= current.dirs.Length then // in-package import up from current directory
                Ok { package = current.package
                     dirs = List.take (current.dirs.Length - ups.Count) current.dirs @ dirs
                     file = file }
            else // to many up steps from current directory
                Error [ for up in ups do yield up.Value ]
        elif isHere then // relative in-package import from current directory  with ./
            Ok { package = current.package 
                 dirs = current.dirs @ dirs
                 file = file }
        else // relative in-package import from current directory
            Ok { package = current.package 
                 dirs = current.dirs @ dirs
                 file = file }


                   