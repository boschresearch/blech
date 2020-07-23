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
    let s1 = @"hello \c world"
    let s2 = @"hello \542 world"
    let s3 = @"hello \xAG world"
    let s4 = @"hello \255 world"
    
    
    [<Test>]
    let testInvalidCharacterEscape () =
        Assert.IsTrue(invalidCharacterEscape.IsMatch s1)
        Assert.IsFalse(invalidCharacterEscape.IsMatch s2)
        Assert.IsFalse(invalidCharacterEscape.IsMatch s3)
        Assert.IsFalse(invalidCharacterEscape.IsMatch s4)
    
    [<Test>]
    let testDecimalEscape () =
        Assert.IsFalse(decimalEscape.IsMatch s1)

        Assert.IsTrue(decimalEscape.IsMatch s2)
        Assert.IsFalse(isValidDecimalEscape <| decimalEscape.Match(s2).Value)

        Assert.IsFalse(decimalEscape.IsMatch s3)

        Assert.IsTrue(decimalEscape.IsMatch s4)
        Assert.IsTrue(isValidDecimalEscape <| decimalEscape.Match(s4).Value)

    [<Test>]
    let testInvalidHexEscape () =
        Assert.IsFalse(invalidHexEscape.IsMatch s1)
        Assert.IsFalse(invalidHexEscape.IsMatch s2)
        Assert.IsTrue(invalidHexEscape.IsMatch s3)
        Assert.IsFalse(invalidHexEscape.IsMatch s4)
        