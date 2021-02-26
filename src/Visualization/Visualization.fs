module Blech.Visualization.Visualization

    open System.IO

    open Blech.Frontend
    open Blech.Frontend.BlechTypes
    open Blech.Common
    open Blech.Visualization.BlechVisGraph
    open Blech.Visualization.Translation
    open Blech.Visualization.Optimization

    /// Synthesis start. Has side effects: prints file to current folder.
    let startSynthesis (cliContext: Arguments.BlechCOptions) (arg : Result<TypeCheckContext * BlechModule, Diagnostics.Logger>) (fileName : string) = 

        // Access values.
        let resultTuple : TypeCheckContext*BlechModule = 
            match arg with 
            | Ok a -> a
            | Error b -> failwith("Can not visualize errorous code: " + b.ToString())

        let blechModule : BlechModule = snd resultTuple

        printfn "Found %i functions or activities." (blechModule.funacts.Length)

        // Synthesize the activities.
        let activityNodes : BlechNode list = synthesize cliContext.vis_notUseConnector blechModule.funacts []

        printfn "Synthesized %i activities." (activityNodes.Length)

        // Optimizations take place here.
        printfn "Optimizing.."
        let inlineActivites = cliContext.vis_breakHierOnActCalls && (if blechModule.entryPoint.IsSome then true else printfn "No entry point given, no inlining of activities possible."; false)
        let entryPointName = if blechModule.entryPoint.IsSome then blechModule.entryPoint.Value.name.ToString() else ""
        let optimizedNodes : BlechNode list = optimize cliContext
                                                       inlineActivites 
                                                       entryPointName 
                                                       activityNodes

        // Generate sctx content.
        printfn "Generating .sctx.."
        let sctxString = SctxGenerator.generate optimizedNodes

        //Read file content for documentation purposes
        let origProDoc = match cliContext.vis_includeOrigCode with
                            | true -> "/** \n " + File.ReadAllText(fileName) + "\n */ \n"
                            | false -> ""

        // Print sctx content to a file.
        SctxToFile.putToFile (origProDoc + sctxString) fileName