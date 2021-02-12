module Blech.Visualization.Visualization

    open Blech.Frontend
    open Blech.Frontend.BlechTypes
    open Blech.Common
    open Blech.Visualization.BlechVisGraph
    open Blech.Visualization.Translation
    open Blech.Visualization.Optimization

    /// Synthesis start. Has side effects: prints file to current folder.
    let startSynthesis (arg : Result<TypeCheckContext * BlechModule, Diagnostics.Logger>) (fileName : string )= 

        // Access values.
        let resultTuple : TypeCheckContext*BlechModule = 
            match arg with 
            | Ok a -> a
            | Error b -> failwith("Can not visualize errorous code: " + b.ToString())

        let blechModule : BlechModule = snd resultTuple

        printfn "Found %i functions or activities." (blechModule.funacts.Length)

        // Synthesize the activities.
        let activityNodes : BlechNode list = synthesize blechModule.funacts []

        printfn "Synthesized %i activities." (activityNodes.Length)

        // Optimizations take place here.
        printfn "Optimizing.."
        // TODO without entry point, just do no inlining of activities.
        let entryPointName = if blechModule.entryPoint.IsSome then blechModule.entryPoint.Value.name else failwith "Need entry point for visualization."
        let optimizedNodes : BlechNode list = optimize (entryPointName.ToString()) activityNodes

        // Generate sctx content.
        printfn "Generating .sctx.."
        let sctxString = SctxGenerator.generate optimizedNodes

        // Print sctx content to a file.
        SctxToFile.putToFile sctxString fileName