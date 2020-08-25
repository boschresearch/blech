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

namespace Blech.Common.Tests

open NUnit.Framework
open Blech.Common
open Blech.Common.BlechString // system under test

module Literals =
    [<Literal>]
    let s = "abc
def"


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

//    [<Test>]
//    let testRemoveBackslashNewlineWhitespace () =
//        Assert.AreEqual (
//            "abc\
//def"
//            |> normalizeEndOfLine 
//            |> removeBackslashNewlineWhitespace, 
//            "abcdef"
//            )

//        Assert.AreEqual (
//            "abc\
//             def"
//            |> normalizeEndOfLine 
//            |> removeBackslashNewlineWhitespace, 
//            "abcdef"
//            )

//        Assert.AreNotEqual (
//            // Invisible chars are the danger of this notation
//            "abc\   
//             def"
//            |> normalizeEndOfLine 
//            |> removeBackslashNewlineWhitespace, 
//            "abcdef"
//            )


//        Assert.AreEqual (
//            "abc
//def"
//            |>  normalizeEndOfLine
//            |> removeBackslashNewlineWhitespace, 
//            "abc\ndef"
//            )
//        Assert.AreEqual (
//            "abc
//            def" 
//            |> normalizeEndOfLine
//            |> removeBackslashNewlineWhitespace, 
//            "abc\n            def"
//            )

    [<Test>]
    let testRemoveLineContinuations () =
        Assert.AreEqual (
            "abcdef",
            "abc\092\013\010def"
            |> normalizeEndOfLine 
            |> replaceLineContinuations
            )

        Assert.AreEqual (
            "abcdef",
            "abc\\\r\ndef"
            |> normalizeEndOfLine 
            |> replaceLineContinuations
            )

        Assert.AreEqual (
            "abc    def",
            "abc\092\013\010    def"
            |> normalizeEndOfLine 
            |> replaceLineContinuations
            )

        Assert.AreEqual (
            "abc    def",
            @"abc\
    def"
            |> normalizeEndOfLine 
            |> replaceLineContinuations
            )

    

    let s1 = @"hello \c world"
    let s2 = @"hello \542 world"
    let s3 = @"hello \xAG world"
    let s4 = @"hello \255 world"
 
    [<Test>]
    let testCheckMultiLineString () =
        Assert.AreEqual(
            List.Empty,
            "\nHello\n world"           
            |> checkMultiLineString
            |> snd
            )
        Assert.AreEqual(
            List.Empty,
            "\n\tHello\n\t world"           
            |> checkMultiLineString
            |> snd
            )

        Assert.AreEqual(
            List.Empty,
            "\n\tHello\n\n\t world"           
            |> checkMultiLineString
            |> snd
            )

        Assert.AreEqual(
            [(2, 0)],
                ("\n\tHello\n \n\t world"    // unbalanced white space line a tab is missing    
                |> checkMultiLineString
                |> snd)
            )

        Assert.AreNotEqual(
            List.Empty,
            "\n\tHello\n\t\t world"           
            |> checkMultiLineString
            |> snd
            )

    //[<Test>]
    //let testInvalidDecimalEscape () =
    //    Assert.IsEmpty (getInvalidDecimalEscapes s1)

    //    Assert.IsNotEmpty (getInvalidDecimalEscapes s2)
    //    Assert.IsEmpty (getInvalidDecimalEscapes s3)

    //    Assert.IsEmpty (getInvalidDecimalEscapes s3)

    //    Assert.IsEmpty(getInvalidDecimalEscapes s4)

    //[<Test>]
    //let testInvalidHexEscape () =
    //    Assert.IsEmpty (getInvalidHexEscapes s1)
    //    Assert.IsEmpty (getInvalidHexEscapes s2)
    //    Assert.IsNotEmpty (getInvalidHexEscapes s3)
    //    Assert.IsEmpty (getInvalidHexEscapes s4)

    //[<Test>]
    //let testGetExtraWhitespaceLength () =
    //    Assert.AreEqual ( 4, getExtraWhitespaceLength "\t\t  " )
    //    Assert.AreEqual ( 2, getExtraWhitespaceLength "\t\t" )
    //    Assert.AreEqual ( 2, getExtraWhitespaceLength "  " )
    //    Assert.AreEqual ( 0, getExtraWhitespaceLength "" )
    //    Assert.AreEqual ( 0, getExtraWhitespaceLength "\t\t  abc" )
        
    [<Test>]
    let testUnescapeNormalizedStringLiteral () =
        Assert.AreEqual (
            "abc\ndef",
            "abc
def"
            |> normalizeEndOfLine
            |> unescapeStringLiteral
            )

        Assert.AreEqual (
            "abcdef", 
            @"abc\
def"
            |> normalizeEndOfLine
            |> unescapeStringLiteral
            )

    [<Test>]
    let testNormalizeMultiLineString () =
        Assert.AreEqual (
            "  Hello,\n  world.\n",
            "
              Hello,
              world.
            "
            |> normalizeMultiLineString
            )
        
        Assert.AreEqual (
            "    This\nis\n  a test",
            "    This
                 is
                   a test"
            |> normalizeMultiLineString
            )

        Assert.AreEqual (
            "hello",
            "
            hello"
            |> normalizeMultiLineString
            )

        Assert.AreEqual (
            "\nhello",
            "

            hello"
            |> normalizeMultiLineString
            )

        Assert.AreEqual (
            "hello\n\nworld",
            "
            hello

            world"
            |> normalizeMultiLineString
            )

        Assert.AreEqual (
             "  hello\n\n  world\n",
             "
               hello

               world
             "
             |> normalizeMultiLineString
             )

        Assert.AreEqual (
             "  hello\n    \n  world\n",
             "
               hello
                 
               world
             "
             |> normalizeMultiLineString
             )

        Assert.AreEqual (
             "hello\n  \nworld",
             "
               hello
                 
               world"
             |> normalizeMultiLineString
             )

        Assert.AreEqual (
            "Hello,\nworld.",
            "
              Hello,
              world."
            |> normalizeMultiLineString
            )
