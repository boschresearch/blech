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
open Blech.Common.Bindings // system under test

[<TestFixture>]
module BindingsTest =
    
    [<Test>]
    let testGetIndexes () =
        let binding = "do { strcpy($2->buf, $1->buf); $2->len = $1->len; } while (0)"
        let idcs = getParameterIndices binding

        Assert.AreEqual(2, idcs.[0])   
        Assert.AreEqual(1, idcs.[1])   
        Assert.AreEqual(2, idcs.[2])   
        Assert.AreEqual(1, idcs.[3])   
    
    [<Test>]
    let testReplace () =
        let binding = "do { strcpy($2->buf, $1->buf); $2->len = $1->len; } while (0)"
        let ids = ["a"; "b"]
        let code = replaceParameters binding ids
        Assert.AreEqual(code, "do { strcpy(b->buf, a->buf); b->len = a->len; } while (0)")
        // to few parameters
        let code = replaceParameters binding ["x"]
        Assert.AreEqual(code, "do { strcpy($2->buf, x->buf); $2->len = x->len; } while (0)")

        let binding2 = "strncpy(*($1).buf, *($2).buf, $3)"
        let exprs = ["a"; "f()"; "42"]
        let code2 = replaceParameters binding2 exprs
        Assert.AreEqual(code2, "strncpy(*(a).buf, *(f()).buf, 42)")