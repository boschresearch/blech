namespace Blech.Frontend

module Export = 

    open Blech.Frontend.CommonTypes

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
    type Types = Map<Name, Visibility * IsSimple>
    
    // exposed and and implicitly exported opaque singletons
    // the names are functions and activities
    type Singletons = Map<Name, Visibility * List<Name>>

    type Signature = 
        { 
            imports: Imports
            code: Code 
            types: Types 
            singletons: Singletons 
        }
    
    let initialiseSignature () : Signature = 
        { 
            imports = Set.empty
            code = Set.empty 
            types = Map.empty
            singletons = Map.empty 
        }