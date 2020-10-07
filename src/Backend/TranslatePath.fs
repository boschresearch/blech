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


let private separateAndExtend sep (moduleName: TranslationUnitPath) extension =
    sprintf "%s%s" (String.concat sep moduleName.AsList) extension
      
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
    separateAndExtend (string Path.DirectorySeparatorChar)moduleName cFileExtension

/// creates a suituable interface file name from a module name, has to be combined with the output directory
let moduleToInterfaceFile (moduleName: TranslationUnitPath) = 
    sprintf "%s%s" (String.concat (string Path.DirectorySeparatorChar) moduleName.AsList) interfaceFileExtension 
    
/// creates a suitable C implementation file name from an app name, has to be combined with the output directory
let appNameToCFile appName = 
    sprintf "%s%s" appName cFileExtension
