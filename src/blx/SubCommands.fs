namespace Blech.Commands

module SubCommands =

    open Argu



    type InitArgs = 
        | [<Unique; AltCommandLine("-pd")>] Project_Dir of directory : string 

        static member DefaultProjectDir = "."
        
        interface IArgParserTemplate with
            member this.Usage =
                match this with
                | Project_Dir _ ->
                    "Create Blech project in <directory>, "
                    + "defaults to " + "\"" + InitArgs.DefaultProjectDir + "\"" + "."


    type FormatArgs = 
        | [<Last; Unique; MainCommand>] Input of filename : string
        
        static member DefaultProjectDir = "."
        
        interface IArgParserTemplate with
            member this.Usage =
                match this with
                | Input _ -> 
                    "File <filename> to be formatted."


    type BlxArgs =
        | Version
        | [<AltCommandLine("-v")>] Verbose
        | [<CliPrefix(CliPrefix.None)>] Init of ParseResults<InitArgs>
        | [<CliPrefix(CliPrefix.None)>] Format of ParseResults<InitArgs>

        interface IArgParserTemplate with
            member this.Usage =
                match this with
                | Version -> 
                    "Displays version information."
                | Verbose -> 
                    "Shows detailed information about operations."
                | Init _ -> 
                    "Create or reinitialize a Blech project directory."
                | Format _ -> 
                    "Format a Blech source file."

    let parser = ArgumentParser.Create<BlxArgs>(programName = "blx")
