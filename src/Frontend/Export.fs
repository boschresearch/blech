namespace Blech.Frontend

module Export = 

    open Blech.Frontend.CommonTypes

    module Env = SymbolTable.Environment

    type Visibility =
        | Transparent         // types, constants
        | Opaque              // types, functions, activitities  

    type private IsSimple = bool
    [<Literal>]
    let isSimple: IsSimple = true
    [<Literal>]
    let isNotSimple: IsSimple = false

    // Required Imports
    type Imports = Set<Name>
    
    // Exposed constants, parameters, functions, activities
    type Code = Set<Name>
    
    // Exposed types and implicitly exported oqaque tpyes
    type Types = Map<Name, Visibility>
    
    // exposed and and implicitly exported opaque singletons
    // the names are functions and activities
    type Singletons = Map<Name, Visibility * List<Name>>

    type Signature = 
        { 
            imports: Set<Name>
            simpleTypes: Map<Name, IsSimple>
            members: Map<Name, Visibility>
            types: Map<Name, Visibility>
            singletons: Map<Name, Set<Name>>
        }
    
    let initialiseSignature () : Signature = 
        { 
            imports = Set.empty
            simpleTypes = Map.empty
            members = Map.empty
            types = Map.empty
            singletons = Map.empty 
        }


    type NameAccessibility =
    | Open
    | SemiOpen 
    | Closed

    
    let private checkCompilationUnit ctx (cu: AST.CompilationUnit) =
        if Option.isNone cu.spec  then 
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