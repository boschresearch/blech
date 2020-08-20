﻿// Copyright (c) 2019 - for information on the respective copyright owner
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

module Blech.Common.SearchPath
    
open System
open System.IO
open System.Text
    
let dot = '.'     // module name separator
let slash = '/'   // directory separator in includes and frompaths
let underscore = '_' //directory separator in include guards
let glob = '?'
let dirSep = ';'  // directory separator for searchpaths

let implementationFileExtension = ".blc"
let interfaceFileExtension = ".blh"
let hFileExtension = ".h"
let cFileExtension = ".c"
let hGuardExtension = "_H_INCLUDED"
let blech = "blech"  // reserved name and keyword for code generation purposes

let blechIdRegex = RegularExpressions.Regex @"^_*[a-zA-Z]+[_a-zA-Z0-9]*$"

type ModuleName = string list

/// Checks if a directory or file name - without extension - can be used as a Blech identifier
let isValidFileOrDirectoryName name = 
    not (name.Equals blech) && (blechIdRegex.IsMatch name) 


/// Returns the list of source directories in a search path.
/// For example: searchPath = ".;../otherSources" -> [".", "../otherSources"] 
let searchPath2Dirs (searchPath: string): string list =
    List.ofArray <| searchPath.Split dirSep    


/// Creates a module name from a list of ids
let moduleNameToString ids =
    String.concat (string dot) ids

/// Replaces '.' in a module name by another separator.
/// For example a.b.c -> a/b/c if seperator = '/'
let replaceSeparator oldSep newSep moduleName =
    let sep2Rep char = 
        if char = oldSep then 
            newSep
        else 
            char 
    String.map sep2Rep moduleName

 
/// creates a search path template from a directory
let mkTemplate dir suffix = 
    let globPattern = sprintf "%c%s" glob suffix 
    Path.Combine [|dir; globPattern|]


    
/// Calculates a filename from a partial filename and a file path template 'template'.
/// For example: patrial filename = "a/b" template = "./?.blc" -> filename = "./a/b.blc" 
let fileName partialFileName template =
    let globToPartialFileName char =
        if char = glob then
            partialFileName
        else 
            string char
    String.collect globToPartialFileName template 


/// Test if file name can be opened for reading
let canOpen fileName =
    try
        let f = File.OpenRead(fileName)
        f.Close()
        true
    with
    | _ -> 
        false


/// Returns the resulting name of the first file with the given suffix in the searchPath that it can open in read mode (after closing it)
/// in case of error it returns a list of file names it tried to open    
let searchFile partialFileName (searchPath: String) extension =
    let dirs = searchPath2Dirs searchPath
    let templates = List.map (fun dir -> mkTemplate dir extension) dirs  
    let filesToTry = List.map (fileName partialFileName) templates
        
    match List.tryFind canOpen filesToTry with
    | Some file ->
        Ok file
    | None ->
        Error filesToTry


let search searchPath name extension =
    //let partialFileName = replaceSeparator dot Path.DirectorySeparatorChar name 
    let partialFileName = String.concat (string Path.DirectorySeparatorChar) name
    searchFile partialFileName searchPath extension 

/// Returns the resulting name of the first implementation file in the searchPath that it can open in read mode (after closing it)
/// in case of error it returns a list of file names it tried to open    
let searchImplementation searchPath (name: ModuleName) = 
    search searchPath name implementationFileExtension

/// Returns the resulting name of the first interface file in the searchPath that it can open in read mode (after closing it)
/// in case of error it returns a list of file names it tried to open   
let searchInterface searchPath (name: ModuleName) = 
    search searchPath name interfaceFileExtension
      
let private separateAndExtend sep (moduleName: ModuleName) extension =
    sprintf "%s%s" (String.concat sep (blech::moduleName)) extension 
      
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
    
/// creates a suitable C implementation file name from a module name, has to be combined with the output directory
let moduleToCFile moduleName = 
    separateAndExtend (string Path.DirectorySeparatorChar)moduleName cFileExtension


/// creates a suituable interface file name from a module name, has to be combined with the output directory
let moduleToInterfaceFile moduleName = 
    sprintf "%s%s" (String.concat (string Path.DirectorySeparatorChar) moduleName) interfaceFileExtension 
    

/// creates a suitable C implementation file name from an app name, has to be combined with the output directory
let appNameToCFile appName = 
    sprintf "%s%s" appName cFileExtension

/// Returns all candidates for source directories, combined from all search directories and a package name
let private sourceDirs searchPath package =
    let searchDirs = searchPath2Dirs searchPath
    List.map (fun sd -> Path.Combine(sd, package)) searchDirs


let private tryGetFullPath path = 
    try
        Some <| Path.GetFullPath(path)
    with
    | _ ->
        None


let private fileIsInSrcDir file srcDir =
    let fsd = tryGetFullPath srcDir
    let ff = tryGetFullPath file
    match ff, fsd with
    | Some f, Some sd ->
        f.StartsWith sd
    | _, _ ->
        false


let private fileToModuleName file srcDir =
    let ff = Path.GetFullPath file
    let fsd = Path.GetFullPath srcDir
    let modFileName = ff.Remove(0, fsd.Length)
                        .TrimStart([|Path.DirectorySeparatorChar|])
    let extLen = implementationFileExtension.Length
    let ids = List.ofArray <| modFileName.Remove(modFileName.Length - extLen, extLen)   
                                         .Split(Path.DirectorySeparatorChar)
    let wrongIds = List.filter (fun id -> not <| isValidFileOrDirectoryName id) ids
    if List.isEmpty wrongIds then
        Ok ids        
    else
        Error wrongIds


let getModuleName searchPath package file : Result<ModuleName, string list> =
    let srcDirs = sourceDirs searchPath package
    let srcDir = 
        match List.tryFind (fun sd -> fileIsInSrcDir file sd) srcDirs with
        | None ->
            Error []
        | Some srcDir -> 
            Ok srcDir
    Result.bind (fileToModuleName file) srcDir    


//let getFileName searchDir package moduleName extension : string = 
//    let filePath = separateAndExtend (string Path.DirectorySeparatorChar) moduleName extension
//    Path.Combine (searchDir, package, filePath)

let moduleNameToIdentifiers (moduleName: string) =
    moduleName.Split dot

let isImplementation (file: string) = 
    (Path.GetExtension file) = implementationFileExtension

let isInterface (file: string) =
    (Path.GetExtension file) = interfaceFileExtension
