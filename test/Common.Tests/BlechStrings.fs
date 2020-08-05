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
    let testNormalizeStringLiteral () =
        Assert.AreEqual (
            "abcdef",
            "abc\092\013\010def"
            |> normalizeEndOfLine 
            |> normalizeStringLiteral
            )

        Assert.AreEqual (
            "abc    def",
            "abc\092\013\010    def"
            |> normalizeEndOfLine 
            |> normalizeStringLiteral 
            )

        Assert.AreEqual (
            "abc    def",
            @"abc\
    def"
            |> normalizeEndOfLine 
            |> normalizeStringLiteral 
            )

    

    let s1 = @"hello \c world"
    let s2 = @"hello \542 world"
    let s3 = @"hello \xAG world"
    let s4 = @"hello \255 world"
 
    [<Test>]
    let testInvalidCharacterEscape () =
        Assert.IsNotEmpty (getInvalidCharacterEscapes s1)
        Assert.IsEmpty (getInvalidCharacterEscapes s2)
        Assert.IsEmpty (getInvalidCharacterEscapes s3)
        Assert.IsEmpty (getInvalidCharacterEscapes s4)
        Assert.IsNotEmpty (
            // blanks ' ' after backslash '\\' 
            "abc\\   
            def"
            |> normalizeEndOfLine
            |> getInvalidCharacterEscapes
            )
        Assert.IsEmpty (
            // end of line after backslash '\\'
            "abc\\
            def"
            |> normalizeEndOfLine
            |> getInvalidCharacterEscapes
            )

    [<Test>]
    let testInvalidDecimalEscape () =
        Assert.IsEmpty (getInvalidDecimalEscapes s1)

        Assert.IsNotEmpty (getInvalidDecimalEscapes s2)
        Assert.IsEmpty (getInvalidDecimalEscapes s3)

        Assert.IsEmpty (getInvalidDecimalEscapes s3)

        Assert.IsEmpty(getInvalidDecimalEscapes s4)

    [<Test>]
    let testInvalidHexEscape () =
        Assert.IsEmpty (getInvalidHexEscapes s1)
        Assert.IsEmpty (getInvalidHexEscapes s2)
        Assert.IsNotEmpty (getInvalidHexEscapes s3)
        Assert.IsEmpty (getInvalidHexEscapes s4)

    [<Test>]
    let testUnescapeNormalizedStringLiteral () =
        Assert.AreEqual (
            "abc\ndef",
            "abc
def"
            |> normalizeEndOfLine
            |> normalizeStringLiteral 
            |> unescapeNormalizedStringLiteral
            )

        Assert.AreEqual (
            "abcdef", 
            @"abc\
def"
            |> normalizeEndOfLine
            |> normalizeStringLiteral
            |> unescapeNormalizedStringLiteral
            )

    let removeTripleQuotes (str: string) = 
        str.Substring(3, str.Length - 6)

    [<Test>]
    let testNormalizeTripleQuotedStringLiteral () =
        Assert.AreEqual (
            "  Hello,\n  world.\n",
            "\"\"\"
              Hello,
              world.
            \"\"\""
            |> normalizeEndOfLine
            |> normalizeTripleQuotedStringLiteral
            |> removeTripleQuotes
            )
        
        Assert.AreEqual (
            "    This\nis\n  a test",
            "\"\"\"    This
                 is
                   a test\"\"\""
            |> normalizeEndOfLine
            |> normalizeTripleQuotedStringLiteral
            |> removeTripleQuotes
            )

        Assert.AreEqual (
            "hello",
            "\"\"\"
            hello\"\"\""
            |> normalizeEndOfLine
            |> normalizeTripleQuotedStringLiteral
            |> removeTripleQuotes
            )

        Assert.AreEqual (
            "\nhello",
            "\"\"\"

            hello\"\"\""
            |> normalizeEndOfLine
            |> normalizeTripleQuotedStringLiteral
            |> removeTripleQuotes
            )

        Assert.AreEqual (
            "Hello,\nworld.",
            "\"\"\"
              Hello,
              world.\"\"\""
            |> normalizeEndOfLine
            |> normalizeTripleQuotedStringLiteral
            |> removeTripleQuotes
            )
