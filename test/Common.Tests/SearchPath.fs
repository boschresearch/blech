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

namespace Blech.Common.Tests

open NUnit.Framework
open System.IO
open Blech.Common
open SearchPath // system under test

[<TestFixture>]
module SearchPathTest =

    let replace (path: string) = path.Replace('/', Path.DirectorySeparatorChar)

    let path = replace ".;C:/somewhere"

    let cur = Directory.GetCurrentDirectory()
    let fileA = Path.Combine(cur, "a.blc")
    let dirA = Path.Combine(cur, "a")
    let fileB = Path.Combine(dirA, "b.blc")
    
    [<SetUp>]
    let createDirAndFiles() =
        ignore <| Directory.CreateDirectory(dirA)
        let a = File.Create(fileA)
        let a_b = File.Create(fileB)
        a.Close()
        a_b.Close()

    [<TearDown>]
    let deleteDirAndFiles() =
        File.Delete fileB
        File.Delete fileA
        Directory.Delete dirA

    [<Test>]
    let testFileName () =
        let dirs = List.ofArray <| path.Split ";"   
        let templates = List.map (fun dir -> mkTemplate dir ".blc" ) dirs
        
        Assert.AreEqual(replace "./a.blc", fileName "a" templates.[0])   
        Assert.AreEqual(replace "C:/somewhere/a.blc", fileName "a" templates.[1])
        
        Assert.AreEqual(replace "./a/b.blc", fileName (replace "a/b") templates.[0])   
        Assert.AreEqual(replace "C:/somewhere/a/b.blc", fileName (replace "a/b") templates.[1])   
        
    [<Test>]   
    let testSearchImplementation () =

        let getResult result =
            match result with
            | Ok res -> res 
            | Error err ->  String.concat ";" err
        
        // found
        Assert.AreEqual(replace "./a/b.blc", searchImplementation path ["a";"b"] |> getResult)
        Assert.AreEqual(replace "./a.blc", searchImplementation path ["a"] |> getResult)
       
        // not found
        Assert.AreEqual(replace "./c.blc;C:/somewhere/c.blc" , searchImplementation path ["c"] |> getResult )
        
    [<Test>]
    let testFileNames() = 
        Assert.AreEqual( replace "a/b.blh", moduleToInterfaceFile ["a";"b"])
        Assert.AreEqual( replace "a.blh", moduleToInterfaceFile ["a"])
        Assert.AreEqual( replace "blech/a/b.c", moduleToCFile ["a";"b"])
        Assert.AreEqual( replace "blech/a.c", moduleToCFile ["a"])
        Assert.AreEqual( replace "blech/a/b.h", moduleToHFile ["a";"b"])
        Assert.AreEqual( replace "blech/a.h", moduleToHFile ["a"])
        
    [<Test>]
    let testFileToModuleName() =
        
        let getModName searchPath package file =
            getModuleName (replace searchPath) (Some <| replace package) (replace file)
        
        let error err : Result<string list, string list> = Error err
        let okay ok: Result<FromPath.ModuleName, string list> = Ok ok
        
        Assert.AreEqual( okay ["dir";"file"], getModName "." "" "dir/file.blc" ) 
        Assert.AreEqual( okay ["file"], getModName  "./dir" "" "dir/file.blc" )

        // Trailing '/' in searchpath
        let msg = "trailing '/'"
        Assert.AreEqual( okay ["dir";"file"], getModName "./" "" "./dir/file.blc", msg )
        Assert.AreEqual( okay ["file"], getModName  "./dir/" "" "./dir/file.blc", msg )
        
        // outside of searchpath 
        Assert.AreEqual( error [], getModName "../somewhere" "" "a/b.blc", "not in searchpath" ) 
        Assert.AreEqual( okay ["a";"b"], getModName  "../somewhere/;." "" "a/b.blc", "in 2nd patch component")
        
        // ' ' NOT allowed in Blech identifiers and module path components
        let msg = "' ' in module path"
        Assert.AreEqual( error ["my file"], getModName "." "" "my file.blc", msg )
        Assert.AreEqual( error ["my dir"; "my file"], getModName "." "" "my dir/my file.blc", msg )
        Assert.AreEqual( error ["file "], getModName "." "" "file .blc", "' ' in module path", msg )
        Assert.AreEqual( error [" dir"], getModName "." "" " dir/file.blc", "' ' in module path", msg )
        
        
        // '_' allowed in Blech identifiers and module path components
        Assert.AreEqual( okay ["my_file"], getModName "." "" "my_file.blc" )
        Assert.AreEqual( okay ["my_dir";"my_file"], getModName "." "" "my_dir/my_file.blc" )
        
        // '-' NOT allowed in Blech identifiers and module path components
        Assert.AreEqual( error ["my-file"], getModName "." "" "my-file.blc" )
        Assert.AreEqual( error ["my-dir"], getModName "." "" "my-dir/my_file.blc" )
        