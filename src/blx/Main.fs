// Learn more about F# at http://docs.microsoft.com/dotnet/fsharp
namespace Blech.Commands

open System


module Main = 
    open SubCommands
    
    [<EntryPoint>]
    let main argv =
        try
            let results = parser.ParseCommandLine(inputs = argv, raiseOnUsage = true)
            if results.GetAllResults().Length = 0 then
                printfn "%s" <| parser.PrintUsage()
        with e ->
            printfn "%s" e.Message
        0
