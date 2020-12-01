module Blech.Visualization.SctxToFile

    open System.IO

    /// Prints the given string to a file with a .sctx-prefix.
    let putToFile (stringToPrint : string) =
        let fileName = "generatedGraph.sctx"
        printf "Printing the a string to a file called %s."  fileName
        File.WriteAllText(fileName, stringToPrint)