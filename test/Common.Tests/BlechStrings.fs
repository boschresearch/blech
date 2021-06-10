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
open Blech.Common.BlechString // system under test

[<TestFixture>]
module BlechStringTest=

    [<Test>]
    let testNormalizeEndOfline () =
        Assert.AreEqual (normalizeEndOfLine "a \n\r b", "a \n b")
        Assert.AreEqual (normalizeEndOfLine "a \r\n b", "a \n b")
        Assert.AreEqual (normalizeEndOfLine "a \n\n\r b", "a \n\n b")
        Assert.AreEqual (normalizeEndOfLine "a \r\r\n b", "a \n\n b")
        Assert.AreEqual (normalizeEndOfLine "a \r\r b", "a \n\n b")
        Assert.AreEqual (normalizeEndOfLine "a \r\n\r b", "a \n\n b")
        Assert.AreEqual (normalizeEndOfLine "\r\n a \r\r b", "\n a \n\n b")
        Assert.AreEqual (
            "abc
def"
            |> normalizeEndOfLine, 
            "abc\ndef"
            )
        Assert.AreEqual (
            "abc
            def" 
            |> normalizeEndOfLine,
            "abc\n            def"
            )


    [<Test>]
    let testRemoveLineContinuations () =
        Assert.AreEqual (
            "abcdef",
            "abc\092\013\010def"
            |> normalizeEndOfLine 
            |> removeLineContinuations
            )

        Assert.AreEqual (
            "abcdef",
            "abc\\\r\ndef"
            |> normalizeEndOfLine 
            |> removeLineContinuations
            )

        Assert.AreEqual (
            "abc    def",
            "abc\092\013\010    def"
            |> normalizeEndOfLine 
            |> removeLineContinuations
            )

        Assert.AreEqual (
            "abc    def",
            @"abc\
    def"
            |> normalizeEndOfLine 
            |> removeLineContinuations
            )

    

    let s1 = @"hello \c world"
    let s2 = @"hello \542 world"
    let s3 = @"hello \xAG world"
    let s4 = @"hello \255 world"
 
    [<Test>]
    let testFindUnbalancedIndentations () =
        Assert.AreEqual(
            ([] : (int * string) list),
            "\nHello\n world"
            |> splitMultiLineString
            |> findUnbalancedIndentations
            |> snd
            )
        Assert.AreEqual(
            ([] : (int * string) list),
            "\n\tHello\n\t world"           
            |> splitMultiLineString
            |> findUnbalancedIndentations
            |> snd
            )

        Assert.AreEqual(
            ([] : (int * string) list),
            "\n\tHello\n\n\t world"           
            |> splitMultiLineString
            |> findUnbalancedIndentations
            |> snd
            )

        Assert.AreEqual(
            [(2, " ")],
                ("\n\tHello\n \n\t world"    // unbalanced white space line a tab is missing    
                |> splitMultiLineString
                |> findUnbalancedIndentations
                |> snd)
            )
        
        printfn "Critical"
        
        Assert.AreEqual(
            [(2, "\t ")],
            "\n\t\tHello\n\t world"
            |> splitMultiLineString
            |> findUnbalancedIndentations
            |> snd
            )

        Assert.AreEqual(
            [(2, "\t\t ")],
            "\n\tHello\n\t\t world"
            |> splitMultiLineString
            |> findUnbalancedIndentations
            |> snd
            )

        Assert.AreEqual(
            [(2, "\t\t ")],
            "\nHello\n\t\t world"
            |> splitMultiLineString
            |> findUnbalancedIndentations
            |> snd
            )

    [<Test>]
    let testFormatMultiLineString () =
        
        

        Assert.AreEqual (
            "  Hello,\n  world.\n",
            "
              Hello,
              world.
            "
            |> normalizeEndOfLine
            |> splitMultiLineString
            |> formatMultiLineString
            )
        
        Assert.AreEqual (
            "    This\nis\n  a test",
            "    This
                 is
                   a test"
            |> normalizeEndOfLine
            |> splitMultiLineString
            |> formatMultiLineString
            )

        Assert.AreEqual (
            "hello",
            "
            hello"
            |> normalizeEndOfLine
            |> splitMultiLineString
            |> formatMultiLineString
            )

        Assert.AreEqual (
            "\nhello",
            "

            hello"
            |> normalizeEndOfLine
            |> splitMultiLineString
            |> formatMultiLineString
            )

        Assert.AreEqual (
            "hello\n\nworld",
            "
            hello

            world"
            |> normalizeEndOfLine
            |> splitMultiLineString
            |> formatMultiLineString
            )

        Assert.AreEqual (
            "  hello\n\n  world\n",
            "
              hello

              world
            "
            |> normalizeEndOfLine
            |> splitMultiLineString
            |> formatMultiLineString
            )

        Assert.AreEqual (
            "  hello\n    \n  world\n",
            "
              hello
                
              world
            "
            |> normalizeEndOfLine
            |> splitMultiLineString
            |> formatMultiLineString
             )

        Assert.AreEqual (
             "hello\n  \nworld",
             "
               hello
                 
               world"
             |> normalizeEndOfLine
             |> splitMultiLineString
             |> formatMultiLineString
             )

        Assert.AreEqual (
            "Hello,\nworld.",
            "
                Hello,
                world."
            |> normalizeEndOfLine
            |> splitMultiLineString
            |> formatMultiLineString
            )
