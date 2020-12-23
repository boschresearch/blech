module Blech.Visualization.SctxToFile

    open System.IO

    /// Prints the given string to a file with a .sctx-prefix.
    let putToFile (stringToPrint : string) (fileName : string)=
        let fileNameExt = fileName + ".sctx"
        printf "Printing to file %s."  fileNameExt
        File.WriteAllText(fileNameExt, stringToPrint)