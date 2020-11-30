namespace Blech.Frontend

module Export = 

    open Blech.Frontend.CommonTypes

    module Env = SymbolTable.Environment


    type Visibility =
        | Hidden
        | Exposed

    type private IsSimple = bool
    [<Literal>]
    let isSimple: IsSimple = true
    [<Literal>]
    let isNotSimple: IsSimple = false


    type Declared =
    | Import                                  // all imported names
    | Type of Visibility * isSimple: IsSimple // all type declarations
    | Constant of Visibility                  // const and param
    | Singleton of Visibility                 // all declared singletons


    type Defined =
    | RequiredImport
    | OpaqueType of isSimple: IsSimple
    | TransparentType 
    | TransparentConstant
    | OpaqueSingleton 
    | PublicRoutine of calledSingletons: Name list


    type ExportContext = 
        {
            lookupTable : SymbolTable.LookupTable
            declarations : Map<Name, Declared> 
            definitions : Map<Name, Defined>
        }

        static member initialise (lut: SymbolTable.LookupTable) = 
            { 
                lookupTable = lut
                declarations = Map.empty
                definitions = Map.empty
            }


    let private checkCompilationUnit (ctx: ExportContext) (cu: AST.CompilationUnit) =
        if cu.IsModule  then 
            ctx
        else
            ctx 

       // printfn "Namecheck Compilation Unit: %s" <| string cu.moduleName
       // this should create an intermediate scope after the imports, lets call it module scope
       //List.fold checkMember ctx cu.imports
       //|> addModuleScope  // all compilation units get a module scope
       //|> Option.fold checkModuleSpecBefore <| cu.spec
       //|> List.fold checkMember <| cu.members
       //|> Option.fold checkModuleSpecAfter <| cu.spec     // check exposes <identifiers> last 