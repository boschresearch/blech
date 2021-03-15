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


module SearchPathTest

open NUnit.Framework
open System.IO
open Blech.Common.TranslationUnitPath // system under test
open Blech.Backend.TranslatePath // system under test

[<TestFixture>]
type Test () =
    let replace (path: string) = path.Replace('/', Path.DirectorySeparatorChar)

    let path = replace ".;C:/somewhere"

    let cur = Directory.GetCurrentDirectory()
    let fileA = Path.Combine(cur, "a.blc")
    let dirA = Path.Combine(cur, "a")
    let fileB = Path.Combine(dirA, "b.blc")
    
    [<SetUp>]
    member x.createDirAndFiles() =
        ignore <| Directory.CreateDirectory(dirA)
        let a = File.Create(fileA)
        let a_b = File.Create(fileB)
        a.Close()
        a_b.Close()

    [<TearDown>]
    member x.deleteDirAndFiles() =
        File.Delete fileB
        File.Delete fileA
        Directory.Delete dirA

    [<Test>]
    member x.testFileName () =
        let dirs = List.ofArray <| path.Split ";"   
        let templates = List.map (fun dir -> mkTemplate dir ".blc" ) dirs
        
        Assert.AreEqual(replace "./a.blc", fileName "a" templates.[0])   
        Assert.AreEqual(replace "C:/somewhere/a.blc", fileName "a" templates.[1])
        
        Assert.AreEqual(replace "./a/b.blc", fileName (replace "a/b") templates.[0])   
        Assert.AreEqual(replace "C:/somewhere/a/b.blc", fileName (replace "a/b") templates.[1])   
        
    [<Test>]   
    member x.testSearchImplementation () =

        let getResult result =
            match result with
            | Ok res -> res 
            | Error err ->  String.concat ";" err
        
        // found
        let case1 =
            { TranslationUnitPath.package = None
              dirs = ["a"]
              file = "b" }
        Assert.AreEqual(replace "./a/b.blc", searchImplementation path case1 |> getResult)
        let case2 =
            { TranslationUnitPath.package = None
              dirs = []
              file = "a" }
        Assert.AreEqual(replace "./a.blc", searchImplementation path case2 |> getResult)
       
        // not found
        let case3 =
            { TranslationUnitPath.package = None
              dirs = []
              file = "c" }
        Assert.AreEqual(replace "./c.blc;C:/somewhere/c.blc" , searchImplementation path case3 |> getResult )
        
    [<Test>]
    member x.testFileNames() = 
        let case1 =
            { TranslationUnitPath.package = None
              dirs = ["a"]
              file = "b" }
        Assert.AreEqual( replace "a/b.blh", moduleToInterfaceFile case1)
        let case2 =
            { TranslationUnitPath.package = None
              dirs = []
              file = "a" }
        Assert.AreEqual( replace "a.blh", moduleToInterfaceFile case2)
        Assert.AreEqual( replace "a/b.c", moduleToCFile case1)
        let case3 =
            { TranslationUnitPath.package = None
              dirs = ["blech"]
              file = "a" }
        Assert.AreEqual( replace "blech/a.c", moduleToCFile case3)
        Assert.AreEqual( replace "a/b.h", moduleToHFile case1)
        Assert.AreEqual( replace "blech/a.h", moduleToHFile case3)
        
    [<Test>]
    member x.testFileToModuleName() =
        
        
        let error err : Result<TranslationUnitPath, string list> = Error err
        let okay ok: Result<TranslationUnitPath, string list> = Ok ok
        
        Assert.AreEqual( okay { package = None; dirs = ["dir"]; file = "file" }, tryMakeTranslationUnitPath "dir/file.blc" "." None) 
        Assert.AreEqual( okay { package = None; dirs = []; file = "file" }, tryMakeTranslationUnitPath "dir/file.blc" "./dir" None  )

        // Trailing '/' in searchpath
        let msg = "trailing '/'"
        Assert.AreEqual( okay { package = None; dirs = ["dir"]; file = "file" }, tryMakeTranslationUnitPath "./dir/file.blc" "./" None, msg )
        Assert.AreEqual( okay { package = None; dirs = []; file = "file" }, tryMakeTranslationUnitPath "./dir/file.blc" "./dir/" None, msg )
        
        // outside of searchpath 
        // Assert.AreEqual( error [], getModuleName "a/b.blc" "../somewhere" None, "not in searchpath" ) 
        //Assert.AreEqual( okay [None; "a"; "b"], getModName  "../somewhere/;." None "a/b.blc", "in 2nd patch component")
        
        // ' ' NOT allowed in Blech identifiers and module path components
        let msg = "' ' in module path"
        Assert.AreEqual( error ["my file"], tryMakeTranslationUnitPath "my file.blc" "." None, msg )
        Assert.AreEqual( error ["my dir"; "my file"], tryMakeTranslationUnitPath "my dir/my file.blc" "." None , msg )
        Assert.AreEqual( error ["file "], tryMakeTranslationUnitPath "file .blc" "." None, msg )
        Assert.AreEqual( error [" dir"], tryMakeTranslationUnitPath " dir/file.blc" "." None, msg )
        
        
        // '_' allowed in Blech identifiers and module path components
        Assert.AreEqual( okay { package = None; dirs = []; file = "my_file" }, tryMakeTranslationUnitPath "my_file.blc" "." None )
        Assert.AreEqual( okay { package = None; dirs = ["my_dir"]; file = "my_file" }, tryMakeTranslationUnitPath "my_dir/my_file.blc" "." None )
        
        // '-' NOT allowed in Blech identifiers and module path components
        Assert.AreEqual( error ["my-file"], tryMakeTranslationUnitPath "my-file.blc" "." None )
        Assert.AreEqual( error ["my-dir"], tryMakeTranslationUnitPath "my-dir/my_file.blc" "." None )
        