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

namespace Blech.Common

[<RequireQualifiedAccess>]
module Logging =

    // ----------------------------------------------------------------------
    //  definitions and functions related to debugging
    // ----------------------------------------------------------------------

    
    let mutable private log_level = 0
        
    /// set the global log level
    let setLogLevel (verbosity: Arguments.Verbosity) =
        match verbosity with
        | Arguments.Q | Arguments.Quiet -> 
            log_level <- 0
        | Arguments.M | Arguments.Minimal -> 
            log_level <- 2
        | Arguments.N | Arguments.Normal -> 
            log_level <- 4
        | Arguments.D | Arguments.Detailed -> 
            log_level <- 6
        | Arguments.Diag | Arguments.Diagnostic -> 
            log_level <- 8

    /// write a debug output for given source, if the current debug level is at least the given one
    let private log n source msg =
        if log_level < n then ()
        else
            System.Console.ForegroundColor <- System.ConsoleColor.Cyan
            printfn "%s [%s] %s" (System.DateTime.Now.ToLongTimeString ()) source msg
            System.Console.ResetColor ()

    let log2 = log 2
    
    let log4 = log 4
    
    let log6 = log 6
    
    let log8 = log 8

