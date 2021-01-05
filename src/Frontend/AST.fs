// Copyright (c) 2019 - for information on the respective copyright owner
// see the NOTICE file and/or the repository 
// https://github.com/boschresearch/blech.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

module Blech.Frontend.AST

open Blech.Common
open Blech.Common.Range
open Blech.Common.TranslationUnitPath

open Constants
open CommonTypes


/// This module contains the (untyped) abstract syntax tree of Blech.
/// The module has three parts:
///   I. Definitions of all required data structures.
///  II. Functions that help the parser to create parts of the AST.
///      This particularly helps with syntactic sugar such as the "reset" block
/// III. The ASTNode type is a dummy type entirely built as the union of all types defined before.
///      It is required to enable a catamorphism on our AST.
///      Functions that traverse the AST. They are parameterised by other functions that tell what to do during traversal.
///      Generally this design pattern is known as "catamorphism" in functional laguanges.
///      It helps to separate recursive traversal logic from the action logic for each node type.
///
/// Design goals:
/// - The AST structure is completely separate from any functionality that operates on it.
/// - Traversal is independent of the actions carried out for the individual nodes.
///   Hence actions can be developed separately and actions do not need to know the traversal logic.
/// - Changes to the AST may break the traversal but once it is fixed the rest of the code remains the same (unless we change types that have been used before, which obviously changes everything).




//////////////////////////////////////////////////////////////////////////
// I. Data structures
//////////////////////////////////////////////////////////////////////////
    
// Untyped Names //////////////////////////////////////////////////////////

// Static name paths lead through packages and classes only (i.e. entities that contain declarations).
// These are needed in unit expressions and data type expressions to refer to names defined elsewhere.
// These name paths cannot have array accesses or struct field accesses!
// Typically dots.Length = path.Length-1, but they may be same if we use an implicit member access
// Currently we only allow implicit member access for enum and union literals, therefore a dot may only
// be followed by a single name. In the future we might have static entities like types inside reftypes,
// then it might be convenient to allow implicit member accesses where a dot is followed by a whole path

type StaticNamedPath = 
    {
        path: Name list
        dots: range list
        qname: QName option ref
    }
    static member Empty = 
        { path = []; dots = []; qname = ref None }

    member this.identifiers: LongIdentifier =
        List.map (fun n -> n.id) this.path
    
    member this.names = this.path
    
    member this.Range = 
        match this.path, this.dots with
        | ([], _) -> failwith "range of StaticeNamedPath"
        | ([n],[]) -> n.range
        | ([n],[r]) -> unionRanges n.range r
        | (n::ns, r::rs) when ns.Length = rs.Length -> unionRanges r (List.last ns).range // implicit member access
        | (n::ns, _) -> unionRanges n.range (List.last ns).range
    
    member this.dottedPathToString =
        match this.path, this.dots with
        | ([], _) -> failwith "dottedPathToString"
        | ([n],[]) -> n.id
        | ([n],[r]) -> "." + n.id
        | (ns, rs) when ns.Length = rs.Length -> List.fold (fun s (n: Name) -> s + "." + n.id ) "" ns  // implicit member access
        | (h::t, _) -> List.fold (fun s n -> s + "." + n.id ) h.id t
            
            
/// This type allows to mix names, array indices and option chaining

type Access =
    | Name of id:Name
    //| NameOption of id:Name * range:range
    | Point of id:Name * range:range
    //| PointOption of id: Name * range:range
    | Index of index:Expr * range:range
    | StaticIndex of index:Expr * range:range
    //| IndexOption of index:Expr * range:range
    //| StaticIndexOption of index: Expr * range:range
    member this.Range = 
        match this with
        | Name (id=n)
            -> n.Range
        //| NameOption (range=r)
        | Point (range=r)
        //| PointOption (range=r)
        | Index (range=r)
        | StaticIndex (range=r)
        //| IndexOption (range=r)
        //| StaticIndexOption (range=r)
            -> r

and TemporalQualification =
    | Current
    | Previous of prev:range
    | Next of next:range

/// Represents a path of names, e.g. package.globalArray.[4+8].someStruct.field
// This is required for expressions to retrieve a value or assign a value to a specific memory location.
// Contrary to StaticNamedPath the DynamicAccessPath additionally supports indexing into arrays and structs.
and DynamicAccessPath = 
    {
        path: Access list
        timepoint: TemporalQualification
        subexpr: Access list ref
        qname: QName option ref
    } 
    member dap.Range =
        let rpath = 
            match dap.path with
            | [] -> failwith "DynamicAccessPath cannot be empty"
            | [ac] -> ac.Range
            | ac::acs -> unionRanges ac.Range (List.last acs).Range
        match dap.timepoint with
        | Current           -> rpath
        | Previous (prev=rprev) -> unionRanges rprev rpath
        | Next (next=rnext)     -> unionRanges rnext rpath
        
    /// Extracts the leading names of dynamic access path up to the first index
    // This is used to guess the static prefix of the dynamic access path
    // Attention can be empty for wild cards
    member this.leadingNames: Name list =
        let isNamePart noi =
            match noi with
            | Name _ | Point _ -> true
            | Index _ | StaticIndex _ -> false
        let toName noi =
            match noi with
            | Name (id = name) | Point (id = name) -> name
            | Index _ | StaticIndex _ -> failwith "this should never happen"
        List.takeWhile isNamePart this.path         
        |> List.map toName

    member this.pathToString =
        this.leadingNames
        |> List.map (fun name -> name.id)
        |> List.reduce(fun a b -> a + "." + b)

        // helping hack as of 05.06.18
        member this.range = 
            match this.path with
            | Name n :: _ -> n.range
            | [] -> failwith "Dynamic path cannot be empty"
            | _ -> failwith "Dynamic path start with a name"

    
// Types /////////////////////////////////////////////////////////////////
    
/// All the predefined types. Including built-in generic types
and DataType =
    // simple types
    | BoolType of range:range
    | BitvecType of size:BitsType * range:range
    | NaturalType of size:NatType * unit:UnitExpr option * range:range
    | IntegerType of size:IntType * unit:UnitExpr option * range:range
    | FloatType of size:FloatType * unit:UnitExpr option * range:range
    // built-in generic compound types
    | ArrayType of size:Expr * elem:DataType * range:range // static size, value type
    // second-class types, elements are always value types
    | SliceType of elem:DataType * range:range
    | Signal of value:DataType option * range:range
    // named types
    | TypeName of StaticNamedPath
    member datatype.Range =
        match datatype with
        | BoolType (range=r)
        | BitvecType (range=r)
        | NaturalType (range=r)
        | IntegerType (range=r)
        | FloatType (range=r)
        | ArrayType (range=r)
        | SliceType (range=r)
        | Signal (range=r)
            -> r   
        | TypeName path 
            -> path.Range
        
/// Declarations //////////////////////////////////////////////////////////

/// This interface is implemented by every type that represents some declaration
and IDeclarable =
    abstract member Range: range
    abstract member name: Name

and Immutable =
    | Let
    | Const
    | Param
//    | Input

and Mutable = 
    | Var
//    | Output

and Permission = 
    | ReadOnly of ro:Immutable * range:range
    | ReadWrite of rw:Mutable * range:range
    member p.Range =
        match p with
        | ReadOnly (range=r) 
        | ReadWrite (range=r)
            -> r
    /// Indicates if a permission is statically defined at compile time
    member p.IsStatic = 
        match p with
        | ReadOnly (ro = Immutable.Const)
        | ReadOnly (ro = Immutable.Param) ->
            true
        | _ -> 
            false

    member p.IsConst = 
        match p with
        | ReadOnly (ro = Immutable.Const) -> true
        | _ -> false

    member p.IsLet = 
        match p with
        | ReadOnly (ro = Immutable.Let) -> true
        | _ -> false

    member p.IsParam = 
        match p with
        | ReadOnly (ro = Immutable.Param) -> true
        | _ -> false

    member p.IsVar = 
        match p with
        | ReadWrite (rw = Mutable.Var) -> true
        | _ -> false


/// Variable declaration as a static or dynamic member
and VarDecl = 
    {
        range: range
        name: Name
        permission: Permission
        isReference: bool
        isExtern: bool
        datatype: DataType option
        initialiser: Expr option
        annotations: Annotation list
    }
    member this.Range = this.range

    interface IDeclarable with
        member this.Range = this.range
        member this.name = this.name

and EnumTypeDecl = 
    { 
        range: range
        isReference: bool
        name: Name
        rawtype : DataType option
        tags: TagDecl list
        members: Member list
        annotations: Annotation list    
    }
    interface IDeclarable with
        member this.Range = this.range
        member this.name = this.name
    
and TagDecl = 
    {
        range: range
        name: Name
        rawvalue: Expr option
        isDefault: bool
    }
    interface IDeclarable with
        member this.Range = this.range
        member this.name = this.name

and StructTypeDecl = 
    { 
        range: range
        isReference: bool
        name: Name
        fields: Member list
        members: Member list
        annotations: Annotation list
    }
    interface IDeclarable with
        member this.Range = this.range
        member this.name = this.name

and OpaqueTypeDecl = 
    { 
        range: range
        isReference: bool
        name: Name
        //representation: DataType option
        members: Member list
        annotations: Annotation list
    }
    interface IDeclarable with
        member this.Range = this.range
        member this.name = this.name
    
and TypeAliasDecl = 
    { 
        range: range
        isReference: bool
        name: Name
        aliasfor: DataType
        members: Member list
        annotations: Annotation list
    }
    interface IDeclarable with
        member this.Range = this.range
        member this.name = this.name
    
    
/// Unit declaration
and UnitDecl =
    {
        range: range
        name: Name
        definition : UnitExpr option
        annotations : Annotation list
    }
    interface IDeclarable with
        member this.Range = this.range
        member this.name = this.name

/// Clock declaration
and ClockDecl = 
    {
        range: range
        name: Name
        definition: ClockExpr
        annotations: Annotation list
    }
    interface IDeclarable with
        member this.Range = this.range
        member this.name = this.name

    
/// activity, function

and ParamDecl =
    {
        range: range
        name: Name
        isMutable: bool
        // isReference: bool   a parameter is always a reference
        datatype: DataType
        sharing: Name list
    }
    member pd.setImmutable = 
        {pd with isMutable = false}
    interface IDeclarable with
        member this.Range = this.range
        member this.name = this.name

and ReturnDecl =
    {
        range: range
        isReference: bool
        datatype: DataType
        sharing: Name list
    }

and SubProgram = 
    {
        range: range
        isSingleton: bool
        singletons: StaticNamedPath list
        isFunction: bool
        name: Name
        inputs: ParamDecl list
        outputs: ParamDecl list
        result: ReturnDecl option
        body: StmtSequence
        annotations : Annotation list // e.g. @[EntryPoint]
    }
    interface IDeclarable with
        member this.Range = this.range
        member this.name = this.name

and Prototype =
    {
        range: range
        isExtern: bool
        isSingleton: bool
        singletons: StaticNamedPath list
        isFunction: bool
        isOpaque: bool // to distinguish from prototypes of local procedures with empty parameter lists
        name: Name
        inputs: ParamDecl list
        outputs: ParamDecl list
        result: ReturnDecl option
        annotations : Annotation list
    }
    interface IDeclarable with
        member this.Range = this.range
        member this.name = this.name

    

and ModulePath = 
    {
        range: range
        path: TranslationUnitPath
    }

    static member Empty = { range = Range.range0; path = TranslationUnitPath.Empty }
    
    member mp.Range = mp.range

    //member mp.FromPath : TranslationUnitPath = 
    //    let moduleName = List.ofArray <| mp.path.Split [| '/' |]
    //    try 
    //        { TranslationUnitPath.package = List.head moduleName
    //          dirs = moduleName.[1 .. moduleName.Length-2]
    //          file = List.last moduleName}
    //    with
    //    | _ -> failwith "this should never happen"
    //    // TODO: This is a temporary hack for branch feature/modules, improve this fjg 16.09.20


and Import = 
    {
        range: range
        localName: Name
        modulePath: ModulePath
        exposing: Exposing option
    }
    
    member import.Range = import.range


and Exposing = 
    { names: Name list
      range: range }
    
    member this.Range = 
        this.range


/// package members (this also subsumes struct members)
/// The grammar must make sure that no structs are generated with non-struct members.
// The decision to not separate package and struct members on the type level
// comes from the fact that this would result in boiler plate code duplication.
and Member = 
    | Nothing                   // just for the moment to enable parsing, tolerating pattern matching warnings
    | Pragma of Annotation
    | EnumType of EnumTypeDecl
    | StructType of StructTypeDecl
    | OpaqueType of OpaqueTypeDecl
    | TypeAlias of TypeAliasDecl
    | Unit of UnitDecl
    | Clock of ClockDecl
    | Var of VarDecl
    | Subprogram of SubProgram
    | Prototype of Prototype
    
    member m.Range =
        match m with
        | Nothing -> Range.rangeStartup
        | Pragma anno -> anno.Range
        | EnumType m -> m.range
        | StructType m -> m.range
        | OpaqueType m -> m.range
        | TypeAlias m -> m.range
        | Unit m -> m.range
        | Clock m -> m.range
        | Var m -> m.range
        | Subprogram m -> m.range
        | Prototype m -> m.range
    

    member m.isInterface =
        match m with
        | Subprogram sp ->
            false
        | Prototype p ->
            not p.isExtern
        | _ ->
            true
      
    member m.IsAPragma =
        match m with
        | Pragma _ ->
            true
        | _ ->
            false

    //member m.isScope =  
    //    match m with
    //    | EnumType _ 
    //    | StructType _
    //    | TypeAlias _ ->
    //        true
    //    | _ ->
    //        false


and ModuleSpec = 
    {
        range: range
        isSignature: bool
        exposing: Exposing option
    }
    member modspec.Range = modspec.range

    static member Nothing = 
        { range = range.Zero
          isSignature = false
          exposing = Option.None }

/// Blech implementation or interface file
and CompilationUnit = 
    {
        range: range
        moduleName: TranslationUnitPath
        imports: Import list
        spec: ModuleSpec option
        members: Member list 
    }
    member this.Range = this.range
    member this.IsModule = 
        match this.spec with
        | Some modSpec ->
            not modSpec.isSignature
        | None ->
            false
    member this.IsProgram = 
        Option.isNone this.spec
    member this.IsSignature =
        match this.spec with
        | Some modSpec ->
            modSpec.isSignature
        | None ->
            false
        

// Unit expressions //////////////////////////////////////////////////////
    
and UnitExpr =
    | One of range:range
    | Unit of StaticNamedPath
    | Parens of UnitExpr * range:range
    | UnitMul of UnitExpr * UnitExpr
    | UnitDiv of UnitExpr * UnitExpr
    | UnitExp of UnitExpr * Int * range:range
        
    member uexpr.Range =
        match uexpr with
        | One (range = r)
        | UnitExp (range = r)
        | Parens (range = r)
            -> r
        | Unit (p)
            -> p.Range
        | UnitMul (l, r) 
        | UnitDiv (l, r)
            -> unionRanges l.Range r.Range

// Clock expressions //////////////////////////////////////////////////////

and ClockExpr =
    | ClockName of StaticNamedPath
    | Count of Int * range:range
    | UpSample of StaticNamedPath * Int * range:range
    | DownSample of StaticNamedPath * Int * (Int option) * range:range
    | Parens of ClockExpr * range:range
    | Join of ClockExpr list  // list is never empty
    | Meet of ClockExpr list
    member clkExp.Range = 
        match clkExp with
        | ClockName path 
            -> path.Range
        | Count (range = r)
        | UpSample (range = r)
        | DownSample (range = r)
        | Parens (range = r)
            -> r
        | Join clcks 
        | Meet clcks
            -> let fst = List.head clcks
               let lst = List.last clcks
               unionRanges fst.Range lst.Range 

// Expressions ///////////////////////////////////////////////////////////

and Literal =
    | Bool of value:bool * range:range
    | String of value:string * range:range
    // -- numerical constants --
    | Bits of value: Constants.Bits * range:range
    | Int of value: Constants.Int * unit:UnitExpr option * range:range
    | Float of value: Constants.Float * unit:UnitExpr option * range:range
    member l.Range = 
        match l with
        | Bool (range=r)
        | String (range=r)
        | Bits (range=r)
        | Int (range=r)
        | Float (range=r)
            -> r

and LhsInAssignment =
    | Wildcard of range
    | Loc of DynamicAccessPath
    //| FreshLoc of VarDecl  // Used in emit and run statements
    //| EventLoc of DynamicAccessPath
    member this.Range =
        match this with
        | Wildcard r -> r
        | Loc l -> l.Range
        //| FreshLoc lv -> lv.Range
        //| EventLoc l -> l.Range

/// Code refers to executable code
and Code = 
    | Procedure of DynamicAccessPath
    member c.Range = 
        match c with
        | Procedure dynAccPath -> dynAccPath.Range

and StructField = 
    { name: Name
      expr: Expr
      range: range }
    member this.Range = this.range

and ArrayField =
    { index: Expr option
      value: Expr
      range: range }
    member this.Range = this.range
    
and FieldExpr = 
    | ResetFields
    | StructFields of StructField list
    | ArrayFields of ArrayField list

/// General expressions
and Expr =
    | Const of Literal
    | AggregateConst of FieldExpr * range:range // array or struct const
    | SliceConst of index:Expr option * length:Expr option * buffer:DynamicAccessPath * range:range 
    | ImplicitMember of StaticNamedPath 
    // -- variables --
    | Var of DynamicAccessPath
    // -- function call --
    | FunctionCall of Code * Expr list * DynamicAccessPath list * range:range // function or instance name, optional method name and two optional list with arguments
    // --- logical operators ---
    | Not of Expr * range:range        // 'not'  
    | And of Expr * Expr               // 'and' 
    | Or of Expr * Expr                // 'or'
    // -- arithmetic operators --
    | Add of Expr * Expr                // '+' addition
    | Sub of Expr * Expr                // '-' subtraction
    | Mul of Expr * Expr                // '*' multiplication
    | Div of Expr * Expr                // '/' division
    | Mod of Expr * Expr                // '%' modulo
    | Pow of Expr * Expr                // '^' exponentiation
    | Unm of Expr * range:range         // '-' unary minus 
    // --- comparison operators
    | Eq of Expr * Expr                 // '==' equality, can be applied to both logical and numerical, yields logical value 
    | Ieq of Expr * Expr                // '!=' inequality
    | Les of Expr * Expr                // '<' less than
    | Leq of Expr * Expr                // '<=' less or equal
    | Grt of Expr * Expr                // '>' greater than
    | Geq of Expr * Expr                // '>=' greater or equal
    // --- identity operators
    | Ideq of Expr * Expr               // '===' is identical, can be applied to all data types, yields logical value
    | Idieq of Expr * Expr              // '!==' is not identical
    // -- bitwise operators --
    | Band of Expr * Expr               // '&' bitwise and 
    | Bor of Expr * Expr                // '|' bitwise or
    | Bxor of Expr * Expr               // '^' bitwise xor
    | Shl of Expr * Expr                // '<<' left shift
    | Shr of Expr * Expr                // '>>' right shift 
    | Bnot of Expr * range:range        // '~' unary bitwise not  
    // -- advanced bitwise operators --
    | Sshr of Expr * Expr               // '+>>' signed shift right
    | Rotl of Expr * Expr               // '<<>' rotate left
    | Rotr of Expr * Expr               // '<>>' rotate right
    // -- type annotation --
    | HasType of Expr * DataType        // ':' define the type for an expression, e.g. "0x_1 : bits8"  
    // -- type conversions --
    | Convert of Expr * DataType * Behaviour  // convert a given expression into a given type, e.g. "sensors[1].speed as float32[mph]"
    // -- operators on arrays and slices --
    | Len of Expr * range:range         // '#' length
    | Cap of Expr * range:range         // '##' capacity
    // -- parentheses --
    | Parens of Expr * range:range      // '(' <Expr> ')'
    member e.Range = 
        match e with
        | Const literal 
            -> literal.Range
        | ImplicitMember staticNamedPath 
            -> staticNamedPath.Range
        | Var location 
            -> location.Range
        | And (l, r)
        | Or (l, r)
        | Add (l, r)
        | Sub (l, r)
        | Mul (l, r)
        | Div (l, r)
        | Mod (l, r)
        | Pow (l, r)
        | Eq (l, r)
        | Ieq (l, r)
        | Les (l, r)
        | Leq (l, r)
        | Grt (l, r)
        | Geq (l, r)
        | Ideq (l, r)
        | Idieq (l, r)
        | Band (l, r)
        | Bor (l, r)
        | Bxor (l, r)
        | Shl (l, r)
        | Shr (l, r)
        | Sshr (l, r)
        | Rotl (l, r)
        | Rotr (l, r)
            -> unionRanges l.Range r.Range
        | Convert (expr, datatype, _)
        | HasType (expr, datatype)
            -> unionRanges expr.Range datatype.Range
        | AggregateConst (range=r)
        | SliceConst (range=r)
        | FunctionCall (range=r)
        | Not (range=r)
        | Unm (range=r)
        | Bnot (range=r)
        | Len (range=r)
        | Cap (range=r)
        | Parens (range=r)
            -> r

/// Receivers and Conditions

and Receiver =
    | Location of LhsInAssignment
    | FreshLocation of VarDecl
    | ReturnLocation of range 
    member rcv.Range =
        match rcv with
        | Location lhsia -> lhsia.Range
        | FreshLocation vdecl -> vdecl.Range
        | ReturnLocation range -> range

and Condition = 
    | Cond of Expr
    | SignalBinding of VarDecl // TODO: probably needs an Expr because this is not an initialiser, fjg 6.5.20
    | Tick of StaticNamedPath * range:range
    member c.Range = 
        match c with
        | Cond expr 
            -> expr.Range
        | SignalBinding vdecl 
            -> vdecl.range
        | Tick (range=r)
            -> r
   
/// Statements ////////////////////////////////////////////////////////////
and Iterator =
    | In
    | Of

/// A block (or statement sequence) is a list of statments
and StmtSequence = 
    Stmt list

/// Individual statments
and Stmt =
    | Nothing      // for a correct tree after parsing with errors
    | Pragma of Annotation
    // local variable, instance declaration
    | LocalVar of VarDecl
    // actions
    | Assign of range:range * LhsInAssignment * Expr
    | Assert of range:range * Condition list * Expr option // conditions and error message
    | Assume of range:range * Condition list * Expr option
    // TODO: add print statement (fg 20.12.16)
    // pause
    | Await of range:range * Condition list // range condition
    // control flow
    | ITE of range:range * Condition list * StmtSequence * (StmtSequence * bool) // range, condition, if-block, else-block (each possibly empty!), isElseIf
    //| Match of range * Expr * (Pattern * Expr option * StmtSequence) list // range, expression to evaluate, list of cases
    | Cobegin of range:range * (Strength * StmtSequence) list // range, list of threads each being weak/strong with a code block
    | WhileRepeat of range:range * Condition list * StmtSequence // range, condition, loop body
    | RepeatUntil of range:range * StmtSequence * Condition list // range, loop body, conditions, ASSUMPTION endless loop <-> condition list is empty
    | NumericFor of range:range * VarDecl * Expr * Expr * Expr option * StmtSequence
    | IteratorFor of range:range * VarDecl * Iterator * Expr * StmtSequence 
    // observation
    | Preempt of range:range * Preemption * Condition list * Moment * StmtSequence   // range, kind of preemption, abort condition, moment of preemption, body
    // scoping
    | SubScope of range:range * StmtSequence // DO block END, ...for scoping reasons
    // calling
    | ActivityCall of range:range * Receiver option * Code * Expr list * DynamicAccessPath list // range, where to store return values, who to call, inputs, outputs
    | FunctionCall of range:range * Code * Expr list * DynamicAccessPath list // range, who to call, inputs, outputs
    
    //| Emit of range:range * DynamicAccessPath // range, event to emit
    | Emit of range:range * Receiver * Expr option // range, event to emit
    | Return of range:range * Expr option // range, expression to return
        
    member stmt.Range =
        match stmt with
        | Nothing 
            -> range.Zero
        | Pragma anno ->
            anno.Range
        | LocalVar vdecl
            -> vdecl.range
        | Assign (range=r)
        | Assert (range=r)
        | Assume (range=r)
        | Await (range=r)
        | ITE (range=r)
        | Cobegin (range=r)
        | WhileRepeat (range=r)
        | RepeatUntil (range=r)
        | NumericFor (range=r)
        | IteratorFor (range=r)
        | Preempt (range=r)
        | SubScope (range=r)
        | ActivityCall (range=r)
        | FunctionCall (range=r)
        | Emit (range=r)
        | Return (range=r)
            -> r            

// attributes (a.k.a. annotations) ///////////////////////////////////////
   
/// an attribute is a name together with a list of possible arguments
    
and Annotation = 
    | Annotation of attribute: Attribute * range: range // TODO: allow a list of attributes in an annotation (see f#, c#) fjg 20.02.19

    member a.Range = 
        match a with Annotation (range=r) -> r

    member a.Attribute = 
        match a with Annotation (attribute=a) -> a
        
and Attribute = // TODO: allow  a Literal as a positional attribute (standard conform), fjg 20.02.19
    | Key of key:Key * range:range
    | KeyValue of key:Key * value:Literal * range:range
    | Structured of key:Key * attrs:Attribute list * range:range

    member a.Range = 
        match a with
        | Key (range=r) 
        | KeyValue (range=r) 
        | Structured (range=r) -> 
            r            

    override this.ToString() =
        match this with
        | Key (key = k) ->
            sprintf "%s" (k.ToString()) 
        | KeyValue (key = k) ->
            sprintf "%s = ..." (k.ToString())
        | Structured (key = k) ->
            sprintf "%s ( ... ) " (k.ToString())

and Key =
    | Quoted of text:string * range:range
    | Ident of text:string * range:range

    member k.Range = 
        match k with
        | Quoted (range=r) 
        | Ident (range=r)
            -> r

    override this.ToString() =
        match this with
        | Quoted (text = t)
        | Ident (text = t) -> t

//////////////////////////////////////////////////////////////////////////
// II. Helper functions (for syntactic sugar, ranges, etc...)
//////////////////////////////////////////////////////////////////////////
//let private filterOut elem lst =
//    // the grammar only adds one thing at a time and thus we only check the newly added element (list head)
//    match lst with
//    | [] -> []
//    | s :: ss -> if s = elem then ss else lst
    
//let filterOutNothingStmt = filterOut Stmt.Nothing
//let filterOutNothingMember = filterOut Member.Nothing
   
let private isNot nothing elem = not (nothing = elem)

let filterOutNothingStmts stmts =
    List.filter (isNot Stmt.Nothing) stmts

let filterOutNothingMembers members = 
    List.filter (isNot Member.Nothing) members


/// Given a list of Names, create a proper static named path value
let mkStaticNamedPath (names, dots) : StaticNamedPath = 
    {
        path = names
        dots = dots
        qname = ref None
    }

/// Given a list of Access, create a proper dynamic access path value
let mkDynamicAccessPath temporalQualifier nameOrExList  =
    {
        path = nameOrExList
        timepoint = temporalQualifier
        subexpr = ref []
        qname = ref None
    }

/// Shorthand function for grammar
let mkDummyBoolConst = 
    Expr.Const (Bool (false, range0))


/// Shorthand function for grammar 
let makeFromPointedName (staticPath: StaticNamedPath) = 
    let nameList = List.map (fun x -> Access.Name x) staticPath.path
    nameList |> mkDynamicAccessPath Current

/// Shorthand function for grammar rule AccessPath which combines
/// a given StaticNamedPath and a Access list into a proper dynamic access path
let mkFromPointedNameAndOptArrayAccess temporalQualifier (staticPath: StaticNamedPath) nameOrExList  =
    let nameList = List.map (fun x -> Access.Name x) staticPath.path
    nameList @ nameOrExList |> mkDynamicAccessPath temporalQualifier

let mkPreemption range preemption conditionLst body =
    match preemption with
    | Abort ->
        Stmt.Preempt(range, Abort, conditionLst, Before, body)
    | Suspend -> // remove this case?
        Stmt.Preempt(range, Suspend, conditionLst, Before, body)
    | Reset -> // rewrite into abort in a loop
        let name = {id = mkPrefixIndexedNameFrom "abortFinished"; range = range}
        let varDecl =
            LocalVar { 
                VarDecl.range = range
                name = name
                permission = ReadWrite(Mutable.Var, range = range)
                isReference = false
                isExtern = false
                datatype = Some (BoolType range)
                initialiser = None
                annotations = []
            }
        let dynPath = 
            { path = [Name(name)]
              timepoint = Current
              subexpr = ref []
              qname = ref None }
        let lhs = Loc dynPath
        let assignNotYetFinished = Stmt.Assign(range, lhs, Const (Bool(false, range)))
        let assignFinished = Stmt.Assign(range, lhs, Const (Bool(true, range)))
        let untilCond = Var dynPath
        let loop =
            Stmt.RepeatUntil (range, 
                              [Stmt.Preempt(range, 
                                            Abort, 
                                            conditionLst, 
                                            Before, 
                                            assignNotYetFinished :: body @ [assignFinished] )], 
                              [Cond untilCond])
        SubScope(range, [varDecl; loop]) // sub-scoping to match exptected return type Stmt


/// Add unary minus to attribute literal
let addOptSubInt optSub (number: Int) =
    match optSub with
    | None -> number
    | Some _ ->
        match number with
        | IAny (v, Some s) -> IAny (-v, Some <| "-" + s)
        | _ -> failwith "Illegal use of minus for attribute literals"

/// Add unary minus to attribute literal
let addOptSubFloat optSub (float: Constants.Float) =
    match optSub with
    | None -> float
    | Some _ -> 
        match float with
        | FAny (v, Some s) -> FAny (-v, Some <| "-" + s)
        | _ -> failwith "Illegal use of minus for attribute literals"

/// unites and optional range and a range
let optUnionRanges optRange range=
    match optRange with
    | None -> range
    | Some r -> unionRanges r range


let unionRangesPlusOpt leftRng rightRng optRng =
    match optRng with
    | None -> unionRanges leftRng rightRng
    | Some rng -> unionRanges leftRng rng



let numberTypeRange range (optUnitExpr: UnitExpr option) =
    match optUnitExpr with
    | None -> range
    | Some unitExpr -> unionRanges range unitExpr.Range 


let typeDeclRange (annos: Annotation list) modifiers startRange endRange =
    let fstRng = 
        match annos, modifiers with
        | [], None -> 
            startRange
        | [], Some modifierRange ->  
            modifierRange
        | hd::_, _ ->
            hd.Range

    unionRanges fstRng endRange 

//let opaqueTypeRange (annos: Annotation list) modifiers startRange (dt: DataType) =
//    typeAliasDeclRange annos modifiers startRange (dt.Range)
    

let tagDeclRange (name: Name) (optRawExpr: Expr option) optDefaultRange =
    let namerng = name.Range
    match optRawExpr, optDefaultRange with
    | _, Some defrng -> unionRanges namerng defrng
    | Some expr, _   -> unionRanges namerng expr.Range
    | _, _           -> namerng


let subprogramRange (annos: Annotation list) singleton startRange endRange =
    match annos, singleton with
    | [], None ->
        unionRanges startRange endRange
    | [], Some sgltnRange ->
        unionRanges sgltnRange endRange
    | hd::_, _ ->
        unionRanges hd.Range endRange

let callRange optRange range inClose optOutClose =
    let start = match optRange with None -> range | Some rng -> rng
    match optOutClose with
    | None -> unionRanges start inClose
    | Some outClose -> unionRanges start outClose

let tailCallRange start inClose optOutClose =
    callRange None start inClose optOutClose
   
let freshLocationRange (qual: Permission) (name: Name) (optType: DataType option) =
    match optType with
    | None -> unionRanges qual.Range name.Range
    | Some typ -> unionRanges qual.Range typ.Range


let returnRange range (optExpr: Expr option) =
    match optExpr with
    | None -> range
    | Some expr -> unionRanges range expr.Range


let moduleHeadRange range (optExposing: Exposing option) =
    match optExposing with
    | None -> range
    | Some exp -> unionRanges range exp.Range


let importAsRange leftRng rightRng (optExp: Exposing option) =
    match optExp with
    | None -> unionRanges leftRng rightRng
    | Some exp -> unionRanges leftRng exp.Range


let importRange importRng pathRng (optExposing : Exposing option) =
    match optExposing with
    | None -> unionRanges importRng pathRng
    | Some exp -> unionRanges importRng exp.Range 


let compilationUnitRange (imports: Import list) defaultRange (members: Member list) =
    let membersRange (members: Member list) =
        unionRanges (List.head members).Range (List.last members).Range 

    let importsRange (imports: Import list) = 
        unionRanges (List.head imports).Range (List.last imports).Range 
        
    match imports, members with
    | [], [] ->
        defaultRange
    | [],  _ ->
        unionRanges defaultRange  (membersRange  members)
    | _,  [] -> 
        unionRanges (importsRange imports) defaultRange
    | _, _ ->
        unionRanges (importsRange imports) (membersRange members)
    

let externalFunctionRange (annos: Annotation list) externRange inputsRange  optOutputsRange (returns: ReturnDecl option) (onClock: StaticNamedPath option) =
    let endRange = 
        if Option.isSome onClock then
            (Option.get onClock).Range
        elif Option.isSome returns then   
            (Option.get returns).range
        elif Option.isSome optOutputsRange then
            Option.get optOutputsRange
        else
            inputsRange
    match annos with
    | [] ->
        unionRanges externRange endRange
    | hd::_ ->
        unionRanges hd.Range endRange

let prototypeRange (annos: Annotation list) singleton startRange inputsRange optOutputsRange (returns: ReturnDecl option) (onClock: StaticNamedPath option)  =
    let endRange = 
        if Option.isSome onClock then
            (Option.get onClock).Range
        elif Option.isSome returns then   
            (Option.get returns).range
        elif Option.isSome optOutputsRange then
            Option.get optOutputsRange
        else
            inputsRange
            
    match annos, singleton with
    | [], None ->
        unionRanges startRange endRange
    | [], Some sgltnRange ->
        unionRanges sgltnRange endRange
    | hd::_, _ ->
        unionRanges hd.Range endRange


let opaqueSingletonRange (annos: Annotation list) singleton nameRange =
    match annos with
    | [] -> 
        unionRanges singleton nameRange
    | hd::_ ->
        unionRanges hd.Range nameRange


let vardeclRange (annos: Annotation list) keywordRange endRange =
    match annos with
    | [] ->
        unionRanges keywordRange endRange
    | hd::_ ->
        unionRanges hd.Range endRange
 
let clockdeclRange = vardeclRange
let unitdeclRange = vardeclRange

//-------------------------
// helpers for dummies required for synactic error handling
//-------------------------

let DummyType = BoolType range.Zero
let DummyRange = range.Zero
    

//////////////////////////////////////////////////////////////////////////
// III. The ASTNode wrapper for above types along with traversal functions
//////////////////////////////////////////////////////////////////////////

type ASTNode = 
    | Package of CompilationUnit
    | Import' of Import
    | Member' of Member
    | Subprogram of SubProgram
    | Prototype of Prototype
    | Stmt of Stmt
    | VarDecl' of VarDecl
    | ParamDecl of ParamDecl
    | ReturnDecl of ReturnDecl
    | UnitDecl of UnitDecl
    | ClockDecl of ClockDecl
    | EnumTypeDecl' of EnumTypeDecl
    | TagDecl of TagDecl
    | StructTypeDecl' of StructTypeDecl
    | OpaqueTypeDecl' of OpaqueTypeDecl
    | TypeAliasDecl' of TypeAliasDecl
    | Receiver of Receiver
    | Lexpr' of LhsInAssignment
    | Expr' of Expr
    | Condition of Condition
    | DataType' of DataType
    | UnitExpr' of UnitExpr
    | ClockExpr' of ClockExpr
    | Annotation' of Annotation

// end of AST data structures

/// Postorder (i.e. bottom-up) AST walker.
let rec postOrderWalk           fNothing fPragma fPackage fImport fPackageMember fSubprogram fFunctionPrototype fStmt fLocalVar fAssign fAssert fAssume fAwait fITE fMatch fCobegin fWhile fRepeat fNumericFor fIteratorFor fPreempt fSubScope fActCall fFunCall fEmit fReturn fVarDecl fParamDecl fReturnDecl fUnitDecl fClockDecl fEnumTypeDecl fTagDecl fStructTypeDecl fOpaqueTypeDecl fTypeAliasDecl fReceiver fLexpr fExpr fCondition fDataType fUnitExpr fClockDef fAnnotation treeNode : 'r=
    let recurse = postOrderWalk fNothing fPragma fPackage fImport fPackageMember fSubprogram fFunctionPrototype fStmt fLocalVar fAssign fAssert fAssume fAwait fITE fMatch fCobegin fWhile fRepeat fNumericFor fIteratorFor fPreempt fSubScope fActCall fFunCall fEmit fReturn fVarDecl fParamDecl fReturnDecl fUnitDecl fClockDecl fEnumTypeDecl fTagDecl fStructTypeDecl fOpaqueTypeDecl fTypeAliasDecl fReceiver fLexpr fExpr fCondition fDataType fUnitExpr fClockDef fAnnotation
    match treeNode with
    | Package p -> 
        let result = List.map (fun m -> recurse (ASTNode.Member' m)) p.members
        fPackage (p.range, p.spec, result)
    | Import' i ->
        fImport i
    | Member' m -> 
        match m with
        | Member.Nothing ->
            fNothing
        | Member.Pragma anno ->
            fPragma anno
        //| Member.Import i->
        //    fImport i
        | Member.EnumType e ->
            fPackageMember (recurse (ASTNode.EnumTypeDecl' e))
        | Member.StructType s ->
            fPackageMember (recurse (ASTNode.StructTypeDecl' s))
        | Member.OpaqueType t ->
            fPackageMember (recurse (ASTNode.OpaqueTypeDecl' t))
        | Member.TypeAlias t ->
            fPackageMember (recurse (ASTNode.TypeAliasDecl' t))
        | Member.Unit u ->
            fPackageMember (recurse (ASTNode.UnitDecl u))
        | Member.Clock c ->
            fPackageMember (recurse (ASTNode.ClockDecl c))
        | Member.Var c ->
            fPackageMember (recurse (ASTNode.VarDecl' c))
        | Member.Subprogram f ->
            fPackageMember (recurse (ASTNode.Subprogram f))
        | Member.Prototype f ->
            fPackageMember (recurse (ASTNode.Prototype f))
    | Subprogram f -> 
        let resIn = List.map (fun i -> recurse (ASTNode.ParamDecl i)) f.inputs
        let resOut = List.map (fun o -> recurse (ASTNode.ParamDecl o)) f.outputs
        let resRet = Option.map (fun r -> recurse (ASTNode.ReturnDecl r)) f.result
        let resBody = List.map (fun s -> recurse (ASTNode.Stmt s)) f.body
        let resAtt =  List.map (fun a -> recurse (ASTNode.Annotation' a)) f.annotations
        fSubprogram (f.range, f.isFunction, f.name, resIn, resOut, resRet, resBody, resAtt)
    | Prototype f ->
        let resIn = List.map (fun i -> recurse (ASTNode.ParamDecl i)) f.inputs
        let resOut = List.map (fun o -> recurse (ASTNode.ParamDecl o)) f.outputs
        let resRet = Option.map (fun r -> recurse (ASTNode.ReturnDecl r)) f.result
        let resAtt =  List.map (fun a -> recurse (ASTNode.Annotation' a)) f.annotations
        fFunctionPrototype (f.range, f.name, resIn, resOut, resRet, resAtt)
    | Stmt s -> 
        match s with
        | LocalVar vdecl ->
            let declRes = recurse (ASTNode.VarDecl' vdecl)
            fLocalVar (vdecl.range, declRes)                
        | Assign (range, lhs, rhs) -> 
            let leftRes = recurse (ASTNode.Lexpr' lhs)
            let rightRes = recurse (ASTNode.Expr' rhs)
            fAssign (range, leftRes, rightRes)
        | Assert (range, conds, msg) ->
            let resCond = List.map (fun c -> recurse (ASTNode.Condition c)) conds
            let resMsg = Option.map (fun e -> recurse (ASTNode.Expr' e)) msg
            fAssert (range, resCond, resMsg)
        | Assume (range, conds, msg) ->
            let resCond = List.map (fun c -> recurse (ASTNode.Condition c)) conds
            let resMsg = Option.map (fun e -> recurse (ASTNode.Expr' e)) msg
            fAssume (range, resCond, resMsg)
        // TODO: add print statement (fg 21.12.16)
        // pause
        | Await (range, conds) ->
            let resultConds = List.map (fun c -> recurse (ASTNode.Condition c)) conds
            fAwait (range, resultConds)
        // control flow
        | ITE (range, conds, bodyIf, (bodyElse, isElseIf)) ->
            let resultConds = List.map(fun c -> recurse (ASTNode.Condition c)) conds
            let resultIf = List.map (fun s -> recurse (ASTNode.Stmt s)) bodyIf
            let resultElse = List.map (fun s -> recurse (ASTNode.Stmt s)) bodyElse
            fITE (range, resultConds, resultIf, resultElse, isElseIf)
        | Cobegin (range, blockList) ->
            let recurseBlock stmts =
                List.map (fun s -> recurse (ASTNode.Stmt s)) stmts
            let result = 
                blockList
                |> List.map (fun (strength, stmts) -> (strength, recurseBlock stmts ) )
            fCobegin (range, result)
        | WhileRepeat (range, conds, body) ->
            let resultCond = List.map (fun c -> recurse (ASTNode.Condition c)) conds
            let result = List.map (fun s -> recurse (ASTNode.Stmt s)) body
            fWhile (range, resultCond, result)
        | RepeatUntil (range, body, conds) ->
            let result = List.map (fun s -> recurse (ASTNode.Stmt s)) body
            let resultConds = List.map (fun c -> recurse (ASTNode.Condition c)) conds
            fRepeat (range, result, resultConds)
        | NumericFor (range, var, init, limit, step, body) ->
            let resVar = recurse (ASTNode.VarDecl' var)
            let resInit = recurse (ASTNode.Expr' init)
            let resLimit = recurse (ASTNode.Expr' limit)
            let resStep = Option.map (fun e -> recurse (ASTNode.Expr' e)) step
            let result = List.map (fun s -> recurse (ASTNode.Stmt s)) body
            fNumericFor(range, resVar, resInit, resLimit, resStep, result)
        | IteratorFor (range, var, iterator, iterable, body) ->
            let resVar = recurse (ASTNode.VarDecl' var)
            let resSequence = recurse (ASTNode.Expr' iterable)
            let result = List.map (fun s -> recurse (ASTNode.Stmt s)) body
            fIteratorFor(range, iterator, resVar, resSequence, result)
        // observation
        | Preempt (range, preemption, conds, moment, body) ->
            let resultCond = List.map (fun c -> recurse (ASTNode.Condition c)) conds
            let result = List.map (fun s -> recurse (ASTNode.Stmt s)) body
            fPreempt (range, preemption, resultCond, moment, result)
        // scoping
        | Stmt.SubScope (range, body) ->
            let result = List.map (fun s -> recurse (ASTNode.Stmt s)) body
            fSubScope (range, result)
        // calling
        | ActivityCall (range, optReceiver, pname, inputOptList, outputOptList) ->
            let leftRes = Option.map (fun l -> recurse (ASTNode.Receiver l)) optReceiver
            let resIn = List.map (fun i -> recurse(ASTNode.Expr' i)) inputOptList
            let resOut = List.map (fun o -> recurse(ASTNode.Expr' (Expr.Var o))) outputOptList // is this OK?
            fActCall (range, leftRes, pname, resIn, resOut)
        | FunctionCall (range, pname, inputOptList, outputOptList) ->
            let resIn = List.map (fun i -> recurse(ASTNode.Expr' i)) inputOptList
            let resOut = List.map (fun o -> recurse(ASTNode.Expr' (Expr.Var o))) outputOptList // is this OK?
            fFunCall (range, pname, resIn, resOut)
        | Emit(range, receiver, optExpr) ->
            let rcvrRes = recurse (ASTNode.Receiver receiver)
            let optPayloadRes = Option.map (fun rhs -> recurse (ASTNode.Expr' rhs)) optExpr
            fEmit(range, rcvrRes, optPayloadRes)
        | Return (range, expr) ->
            let result = Option.map (fun e -> recurse (ASTNode.Expr' e)) expr 
            fReturn (range, result)
        | Nothing ->
            fNothing
        | Pragma anno ->
            fPragma anno
        |> fStmt
    | VarDecl' v -> 
        let resDataType = Option.map (fun d -> recurse (ASTNode.DataType' d)) v.datatype
        let resInit = Option.map (ASTNode.Expr' >> recurse) v.initialiser
        let resAtt = List.map (fun a -> recurse (ASTNode.Annotation' a)) v.annotations
        fVarDecl (v.range, v.name, v.permission, resDataType, resInit, resAtt)
    | ParamDecl v -> 
        let resDataType = recurse (ASTNode.DataType' v.datatype)
        fParamDecl (v.range, v.name, v.isMutable, resDataType)
    | ReturnDecl r -> 
        let resDataType = recurse (ASTNode.DataType' r.datatype)
        fReturnDecl (r.range, r.isReference, r.sharing, resDataType)
    | UnitDecl u -> 
        let resDef = Option.map (fun d -> recurse (ASTNode.UnitExpr' d)) u.definition
        let resAtt = List.map (fun a -> recurse (ASTNode.Annotation' a)) u.annotations
        fUnitDecl (u.range, u.name, resDef, resAtt)
    | ClockDecl c ->
        let resExpr = recurse (ASTNode.ClockExpr' c.definition)
        let resAtt = List.map (fun a -> recurse (ASTNode.Annotation' a)) c.annotations
        fClockDecl (c.range, c.name, resExpr, resAtt)  
    | EnumTypeDecl' e -> 
        let resRawtype = Option.map (ASTNode.DataType' >> recurse) e.rawtype
        let resTags = List.map (ASTNode.TagDecl >> recurse) e.tags
        let resMembers = List.map (ASTNode.Member' >> recurse) e.members
        let resAtt = List.map (ASTNode.Annotation' >> recurse) e.annotations
        fEnumTypeDecl (e.range, e.isReference, e.name, resRawtype, resTags, resMembers, resAtt)
    | TagDecl t ->
        fTagDecl t
    | StructTypeDecl' s -> 
        let resFields = List.map (ASTNode.Member' >> recurse) s.fields
        let resMembers = List.map (ASTNode.Member' >> recurse) s.members
        let resAtt = List.map (ASTNode.Annotation' >> recurse) s.annotations
        fStructTypeDecl (s.range, s.isReference, s.name, resFields, resMembers, resAtt)
    | OpaqueTypeDecl' t -> 
        // let resDat = Option.map (fun r -> recurse (ASTNode.DataType' r)) t.representation
        let resMembers = List.map (ASTNode.Member' >> recurse) t.members
        let resAtt = List.map (fun a -> recurse (ASTNode.Annotation' a)) t.annotations
        fOpaqueTypeDecl (t.range, t.isReference, t.name, resMembers, resAtt)
    | TypeAliasDecl' t -> 
        let resDat = recurse (ASTNode.DataType' t.aliasfor)
        //let resDat = Option.map (fun r -> recurse (ASTNode.DataType' r)) t.aliasfor
        let resAtt = List.map (fun a -> recurse (ASTNode.Annotation' a)) t.annotations
        fTypeAliasDecl (t.range, t.name, resDat, resAtt) 
    | Receiver r -> 
        fReceiver r
    | Lexpr' l ->
        fLexpr l
    | Expr' e ->
        fExpr e
    | Condition c ->
        fCondition c
    | DataType' d ->
        fDataType d
    | UnitExpr' u ->
        fUnitExpr u
    | ClockExpr' c ->
        fClockDef c
    | Annotation' a -> 
        fAnnotation a
// end of postOrderWalk