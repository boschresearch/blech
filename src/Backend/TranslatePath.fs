// Copyright (c) 2020 - for information on the respective copyright owner
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

//=============================================================================
// This module has all the functions for
// translating the translation unit paths to
// actual file names (.c, .h, .blh)
//=============================================================================
module Blech.Backend.TranslatePath

open System.IO

open Blech.Common.TranslationUnitPath

let private separate sep (moduleName: TranslationUnitPath) =
    String.concat sep moduleName.AsList

let private separateAndExtend sep (moduleName: TranslationUnitPath) extension =
    sprintf "%s%s" (separate sep moduleName) extension
      
/// creates a suituable header file name from a module name, has to be combined with the output directory
let moduleToHFile moduleName =
    separateAndExtend (string Path.DirectorySeparatorChar) moduleName hFileExtension

let moduleToInclude moduleName =
    separateAndExtend (string slash) moduleName hFileExtension
    
let moduleToCFileInclude moduleName = 
    separateAndExtend (string slash) moduleName cFileExtension
    
let moduleToIncludeGuard moduleName = 
    let ig = separateAndExtend (string underscore) moduleName hGuardExtension
    ig.ToUpper()
    |> (fun s -> s.Replace(".", "_"))
    
/// creates a suitable C implementation file name from a module name, has to be combined with the output directory
let moduleToCFile moduleName = 
    separateAndExtend (string Path.DirectorySeparatorChar) moduleName cFileExtension

/// creates a suituable interface file name from a module name, has to be combined with the output directory
let moduleToInterfaceFile (moduleName: TranslationUnitPath) = 
    separateAndExtend (string Path.DirectorySeparatorChar) moduleName interfaceFileExtension
    
/// creates a suitable C implementation file name from an app name, has to be combined with the output directory
let appNameToCFile appName = 
    sprintf "%s%s" appName cFileExtension

// Name mangling for TranslationUnitPath in a generated C name
// prevents naming conflicts
let private BOX = "02" 
let private MOD = "01" 
// "00" is for auxiliary names inside a module

/// creates a the module name part for a C name
/// example: "box:lib/dir/dir/mod" is encode as ["02lib"; "01dir01dir01mod01"]
/// "/dir/dir/mod" is encode as ["01dir01dir01mod01"]
// The encoding is necessary to uniquely identify box names and module names in C code
// This enables name shortening via a macro mechanism
// example #define _02lib _<unique box number for box:lib>
// #define _01dir01dir01mod01 _<unique module number for /dir/dir/mod>
let moduleToCNameParts (moduleName: TranslationUnitPath) = 
    let modul = MOD + (String.concat MOD moduleName.GetModuleSegments) + MOD
    match moduleName.package with
    | None -> [ modul ]
    | Some box -> (BOX + box) :: [ modul ]
