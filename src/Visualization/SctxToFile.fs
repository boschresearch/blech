module Blech.Visualization.SctxToFile

    open System.IO

    /// Prints the given string to a file with a .sctx-prefix.
    let putToFile (stringToPrint : string) =
        let fileName = "generatedGraph.sctx"
        printf "Printing to file %s."  fileName
        File.WriteAllText(fileName, stringToPrint)