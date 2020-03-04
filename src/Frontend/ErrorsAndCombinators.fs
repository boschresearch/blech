﻿// Copyright (c) 2019 - for information on the respective copyright owner
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

///============================================================================
/// This namespace defines all kinds of type checking errors that can be 
/// reported to the user, as well as a Result type "TyChecked" that holds such
/// errors and combination functions on that Result type.
///============================================================================

namespace Blech.Frontend

open Blech.Common
open Blech.Common.Range

open Constants
open CommonTypes
open BlechTypes


//=============================================================================
// Errors
//=============================================================================

type TyCheckError =
    // compiler implementation deficiencies
    | ImpossibleCase of obj
    | UnsupportedFeature of range * string
    | UnsupportedTuple of range
    | IllegalAccessOfTypeInfo of string
    | ExpectedSubProgDecl of range * string
    | AmendBroken of Types * TypedRhs
    //| MissingQName of range * Identifier
    | NoDefaultValueForAny of range * Identifier
    | IllegalVoid of range * Identifier
    | ValueCannotBeVoid of string
    | EmptyGuardList
    // declarations
    | NotInLUTPrevError of string
    | VarDeclMissingTypeOrValue of range * Identifier
    | VarDeclRequiresExplicitType of range * Identifier
    | NoDefaultValueForSecondClassType of range * Identifier * ReferenceTypes
    | MismatchDeclInit of range * Identifier * Types * TypedRhs
    // expressions
    | InvalidFloat of range * string
    | NextOnRhs of range * string
    | PrevOnLhs of range * string
    | NextPrevOnReturn of range
    | MismatchArgNum of range * string * int * int //where, called subprog, parameters given, parameters expected
    | ExprMustBeALocationL of range * TypedLhs
    | ExprMustBeALocationR of range * TypedRhs
    | CannotCallNonVoidFunAsStmt of range * QName
    | CannotModFloats of TypedRhs * TypedRhs
    | CannotResetRefType of range
    | FunCallInExprMustBeNonVoid of range * QName
    | MultipleReturnsInCobegin of range
    | ReturnsInCobegin of range
    | FieldAccessOnNonStructType of Name * TypedMemLoc
    | ArrayAccessOnNonArrayType of range * TypedMemLoc
    | FieldNotAMember of Name * TypedMemLoc
    | FieldNotAMember2 of range * QName * Identifier
    | IndexMustBeInteger of range * TypedRhs * TypedMemLoc
    | StaticArrayOutOfBounds of range * TypedRhs * TypedMemLoc * Size
    | AssignmentToImmutable of range * Identifier
    | AssignmentToLetFields of range * Identifier
    | ImmutableOutArg of range * TypedLhs
    | ConditionHasSideEffect of TypedRhs
    | InitialisationHasSideEffect of TypedRhs
    | NotACompileTimeSize of TypedRhs
    | ReInitArrayIndex of range * Size * Size
    | PrevOnParam of range * QName
    | PrevOnImmutable of range * QName
    | PrevOnlyOnValueTypes of range * Types
    | PrevInFunction of range
    | NeedConstInit of range * Name
    | MustBeConst of TypedRhs
    | ConstArrayRequiresConstIndex of range
    | ParameterMustHaveStaticInit of Name * TypedRhs
    // calls
    | FunCallToAct of range * FunctionPrototype
    | RunAFun of range * FunctionPrototype
    
    // simple types
    | ExpectedBoolExpr of range * TypedRhs
    | ExpectedBitsExpr of TypedRhs
    | UnaryMinusOnNatExpr of range * TypedRhs
    | ExpectedInvertableNumberExpr of range * TypedRhs
    
    // Shift amounts, arrays sizes and indexes
    | NoShiftAmountType of TypedRhs
    
    // Cast and Conversion
    | WrongTypeAnnotation of range * TypedRhs * Types
    | DownCast of range * TypedRhs * Types
    | ImpossibleCast of range * TypedRhs * Types
    
    // bitwise operators
    | BitwiseOperationTypeMismatch of range * TypedRhs * TypedRhs
    | ExpectedBitsArguments of range * TypedRhs * TypedRhs
    

    // types
    | TypeMismatch of Types * TypedRhs
    | TypeMismatchArrStruct of Types * TypedRhs
    | TypeMismatchStructArr of Types * TypedRhs
    | TypeMismatchPrimitiveComposite of Types * TypedRhs
    | AssignTypeMismatch of range * TypedLhs * TypedRhs
    | ArgTypeMismatchR of range * ParamDecl * TypedRhs
    | ArgTypeMismatchL of range * ParamDecl * TypedLhs
    | MustReturnFirstClassType of range * Identifier
    | NonFirstClassReturnStmt of range
    | ValueMustBeOfValueType of TypedLhs
    | ExpectedBoolConds of TypedRhs * TypedRhs
    | MustBeNumeric of TypedRhs * TypedRhs
    | SameTypeRequired of TypedRhs * TypedRhs
    | SameArithmeticTypeRequired of TypedRhs * TypedRhs
    | SameFirstTypeRequired of range * ValueTypes * ValueTypes
    | NoComparisonAllowed of TypedRhs * TypedRhs
    | IncomparableReturnTypes of range * ValueTypes * ValueTypes
    | VoidSubprogCannotReturnValues of range // is actually just a ReturnTypeMismatch with a "void" built in
    | VoidReturnStmtMustReturn of range * Types // is actually just a ReturnTypeMismatch with a "void" built in
    | MustReturnSomething of range * ValueTypes
    | ReturnTypeMismatch of range * ValueTypes * Types
    | ActCallMustExplicitlyIgnoreResult of range * Identifier
    | MayOrMayNotReturn of range * ValueTypes * ValueTypes
    | ValueStructContainsRef of Name * VarDecl
    | ValueArrayMustHaveValueType of range
    | TooManyInitialisers of range * Size
    // statements
    | ExternalsInFunction of range
    | SynchronousStatementInFunction of range
    | ActivityHasInstantaneousPath of range * Name
    
    // --- evaluation ---
    // simple literals
    | LiteralNotInType of TypedRhs * Types
    | LiteralNotInLargestType of TypedRhs * Types
    | NumberLargerThanAnyInt of range * Int
    | NumberLargerThanAnyBits of range * Bits
    | NumberLargerThanAnyFloat of range * Float
    
    // Array sizes and indexes
    | NegativeArrayIndex of TypedRhs
    | PositiveSizeExpected of range * TypedRhs
    | ArraySizeOverflowsWordsize of range * Arguments.WordSize * TypedRhs
    
    // shift amounts
    | NegativeShiftAmount of TypedRhs
    
    // cast and conversions
    | LiteralDoesNotHaveType of range * TypedRhs * Types
    | LiteralCastNotInType of range * TypedRhs * Types
    | LiteralCastNotNecessary of range * TypedRhs * Types

    // arithmetic
    | UnaryMinusOverFlow of range * TypedRhs
    
    | ArithmeticOverFlow of range * TypedRhs * TypedRhs
    | DivideByZero of range * TypedRhs
    
    // bitwise operations
    | UnaryMinusOnBitsLiteral of range * TypedRhs
    | ComplementOnBitsLiteral of range * TypedRhs
    | BitwiseBinaryOperationOnAnyBits of range * TypedRhs * TypedRhs
    | ShiftOperationOnAnyBits of range * TypedRhs
    
    // annotations
    | UnsupportedAnnotation of range
    | MissingAnnotation of range * string
    | MultipleUniqueAnnotation of first: range * second: range
    | MissingNamedArgument of range * string
    | MissingEntryPoint of range
    | MultipleEntryPoints of first: range * second: range
    | IllegalEntryPoint of range * AST.Package
    // pragmas
    | UnknownPragma of range
    // Dummy error used during development
    // | Dummy of range * string

    interface Diagnostics.IDiagnosable with
        member err.MainInformation =
            match err with
            
            | ImpossibleCase o -> Range.range0, sprintf "Seems like some of the DUs in the type checker are not up-to-date. Ran into an seemingly impossible case: %A." o
            | UnsupportedFeature (p, s) -> p, sprintf "Sorry, currently the type checker does not support %s." s
            | UnsupportedTuple p -> p, sprintf "Multiple-return types, assignments or tuples are not supported."
            | IllegalAccessOfTypeInfo s -> Range.range0, sprintf "Internal error: tried to lookup data type for identifier %s which does not represent data." s
            | ExpectedSubProgDecl (p, n) -> p, sprintf "Internal error: expected a subprogram for lookup table entry %s." n
            | AmendBroken (t, r) -> r.Range, sprintf "Could not amend. Type %s Expression %s." (t.ToString()) (r.ToString())
            //| MissingQName (p, id) -> p, sprintf "Internal error: Expected a qualified identifier for %s but found none, buggy name resolution?" id
            | NoDefaultValueForAny (p, n) -> p, sprintf "Internal error: tried to determine a default value for %s which has type any." (string n)
            | IllegalVoid (p, n) -> p, sprintf "Internal error: tried to determine a default value for %s which has type void." (string n)
            | ValueCannotBeVoid n -> Range.range0, sprintf "Internal error: attempted to create a void value for identifier %s." n
            | EmptyGuardList -> Range.range0, sprintf "Making an empty guard expression should be impossible!"
            
            // declarations
            | NotInLUTPrevError s -> Range.range0, sprintf "Identifier %s is not in the lookup table, probably due to a previous error." s 
            | VarDeclMissingTypeOrValue (p, n) -> p, sprintf "The declaration of variable %s needs either a type annotation or an initialisation." (string n)
            | VarDeclRequiresExplicitType (p, n) -> p, sprintf "Could not infer type of %s. Please provide explicit type information." (string n)
            | NoDefaultValueForSecondClassType (p, n, typ) -> p, sprintf "Internal error: tried to determine a default value for %s which has type %s." (string n) (typ.ToString())
            | MismatchDeclInit (p, n, typ, init) -> p, sprintf "%s has type %s but is initialised with %s which is of type %s." (string n) (typ.ToString()) (init.ToString()) (init.typ.ToString())
            
            // expressions
            | InvalidFloat (p, s) -> p, sprintf "%s cannot be parsed as a floating point number." s
            | NextOnRhs (p, s) -> p, sprintf "The access of the next value of %s is forbidden on the right hand side." s
            | PrevOnLhs (p, s) -> p, sprintf "The access of the prev value of %s is forbidden on the left hand side." s
            | NextPrevOnReturn p -> p, sprintf "You cannot use prev or next on a returned value."
            | MismatchArgNum (p, s, given, expected) -> p, sprintf "The call to %s provides %i arguments but %i are expected." s given expected
            | ExprMustBeALocationL (p, l) -> p, sprintf "Expression %s must be an identifier (or reference)." (l.ToString())
            | ExprMustBeALocationR (p, r) -> p, sprintf "Expression %s must be an identifier (or reference)." (r.ToString())
            | CannotCallNonVoidFunAsStmt (p, name) -> p, sprintf "The returned value of %s must be ignored explicitly." (name.ToString())
            | CannotModFloats (expr1, expr2) -> Range.unionRanges expr1.Range expr2.Range, sprintf "Both %s and %s must be integers in order to apply mod." (expr1.ToString()) (expr2.ToString())
            | CannotResetRefType p -> p, "A reference-type variable cannot be re-initialised as a whole."
            | FunCallInExprMustBeNonVoid (p, name) -> p, sprintf "Void subprogram %s cannot be called inside an expression." (name.ToString())
            | MultipleReturnsInCobegin p -> p, "Cobegin may return values from at most one of its blocks."
            | ReturnsInCobegin p -> p, "The return statement is prohibited inside a cobegin statement."
            | FieldAccessOnNonStructType (acc, tml) -> acc.Range, sprintf "%s is not a struct and has no field %s." (tml.ToString()) (acc.ToString())
            | ArrayAccessOnNonArrayType (r, tml) -> r, sprintf "%s is not an array." (tml.ToString())
            | FieldNotAMember (name, tml) -> name.range, sprintf "%s does not have a field %s." (tml.ToString()) name.id
            | FieldNotAMember2 (p, qname, ident) -> p, sprintf "%s does not have a field %s." (qname.ToString()) ident
            | IndexMustBeInteger (r, idx, dPath) -> r, sprintf "The array access [%s] in %s must evaluate to an integer." (idx.ToString()) (dPath.ToBasicString())
            | StaticArrayOutOfBounds (r, idx, dPath, maxIdx) -> r, sprintf "The array access [%s] in %s is out of bounds [0..%s]." (idx.ToString()) (dPath.ToBasicString()) (string maxIdx)
            | AssignmentToImmutable (p, l) -> p, sprintf "%s is immutable and cannot be assigned any value" (l.ToString())
            | AssignmentToLetFields (p, l) -> p, sprintf "%s contains substructures with immutable fields. It therefore cannot be overwritten as a whole." (l.ToString())
            | ImmutableOutArg(p, l) -> p, sprintf "Read-only location %s cannot be passed as an output argument." (l.ToString())
            | ConditionHasSideEffect cond -> cond.Range, sprintf "The condition %s has a side-effect. This is not allowed." (cond.ToString())
            | InitialisationHasSideEffect expr -> expr.Range, sprintf "The initialisation expression %s has a side-effect. This is not allowed." (expr.ToString())
            | NotACompileTimeSize expr -> expr.Range, sprintf "The expression %s cannot be evaluated to a size number at compile time. If you used \"let\" to declare it, use \"const\" instead." (expr.ToString())
            | ReInitArrayIndex (r, given, counter) -> r, sprintf "The array cell in position %d cannot be redefined. The given index must be at least %d at this point." given counter
            | PrevOnParam (r, q) -> r, sprintf "The prev operator can only be applied to local variables, however here it used on parameter %s." (q.ToString())
            | PrevOnImmutable (r, q) -> r, sprintf "The prev operator cannot be applied to immutable variable %s." (q.ToString())
            | PrevOnlyOnValueTypes (r, t) -> r, sprintf "The prev operator can only be applied to value typed variables, however here it used on type %s." (t.ToString())
            | PrevInFunction r -> r, "Operator prev cannot be used inside a function."
            | NeedConstInit (r, n) -> r, sprintf "The initialiser of %s must be constant. Make sure not to use \"let\"-bound or other variables and parameters in it." n.idToString
            | MustBeConst expr -> expr.Range, sprintf "The expression %s must be a compile-time constant." (expr.ToString())
            | ConstArrayRequiresConstIndex r -> r, sprintf "Constant arrays must be accessed using constant indices. Hint: use param arrays if you need dynamic access at runtime."
            | ParameterMustHaveStaticInit (name, checkedInitExpr) -> name.range, sprintf "The static parameter %s was initialised by %s which assumes a value at runtime. Instead it must be initialised using only constants or other static parameters." name.idToString (checkedInitExpr.ToString())
            
            // calls
            | FunCallToAct (p, decl) -> p, sprintf "This is a function call to an activity. Did you mean 'run %s ...'?" (decl.name.basicId)
            | RunAFun (p, _) -> p, sprintf "You can only run an activity, not a function."
            
            // simple types
            | ExpectedBoolExpr (p, r) -> p, sprintf "Expression '%s' must be boolean." (r.ToString())
            | ExpectedBitsExpr expr -> expr.range, sprintf "Given type '%s' is not a bitsX type." (string expr.typ)
            | UnaryMinusOnNatExpr (p, expr) -> p, sprintf "You cannot invert the sign of nat value '%s'" (expr.ToString())
            | ExpectedInvertableNumberExpr (p, expr) -> p, sprintf "You cannot invert the sign of '%s', which is not a number." (expr.ToString())
            
            // Shift amounts, arrays sizes and indexes
            | NoShiftAmountType expr ->
                expr.Range, sprintf "Type '%s' is not a valid type for a shift amount" (string expr.typ)
            
            // Cast and converions
            | WrongTypeAnnotation (rng, expr, typ) -> 
                rng,  sprintf "Type annotation '%s' does not match type '%s' of the given expression." (string typ) (string expr.typ)
            | DownCast (rng, expr, typ) ->
                rng, sprintf "Type conversion 'as' does not allow downcast from type '%s' to type '%s'." (string expr.typ) (string typ)
            | ImpossibleCast (rng, expr, typ) ->
                rng, sprintf "Type conversion from type '%s' to type '%s' not allowed." (string expr.typ) (string typ)
                
            // bitwise operators
            | BitwiseOperationTypeMismatch (rng, lexpr, rexpr) ->
                rng, "Bitwise operation on arguments of different bits size."
            | ExpectedBitsArguments (rng, lexpr, rexpr) -> 
                rng, "Binary bitwise operation requires arguments of the same bitsX type." 
            

            // types
            | TypeMismatch (t, r) -> 
                match r.typ with
                | AnyInt 
                | AnyFloat ->
                    r.Range, sprintf "Type mismatch. The given expression %s is outside the range of expected type %s." (r.rhs.ToString())(t.ToString())
                | _ ->
                    r.Range, sprintf "Type mismatch. %s was expected but the given expression %s is of type %s." (t.ToString())(r.rhs.ToString())(r.typ.ToString())
            | TypeMismatchArrStruct (t, r) -> r.Range, sprintf "Type mismatch. An array of type %s was expected but the struct literal %s was given." (t.ToString())(r.rhs.ToString())
            | TypeMismatchStructArr (t, r) -> r.Range, sprintf "Type mismatch. A struct of type %s was expected but the array literal %s was given." (t.ToString())(r.rhs.ToString())
            | TypeMismatchPrimitiveComposite (t, r) -> r.Range, sprintf "Type mismatch. A value of type %s was expected but a compound literal %s was given." (t.ToString())(r.rhs.ToString())
            | AssignTypeMismatch (p, l, r) -> p, sprintf "Type mismatch. Cannot assign %s to %s." (r.ToString()) (l.ToString())
            | ArgTypeMismatchR (p, a, r) -> p, sprintf "Type mismatch. Cannot instantiate formal parameter %s with %s." (a.name.ToString()) (r.ToString())
            | ArgTypeMismatchL (p, a, l) -> p, sprintf "Type mismatch. Cannot instantiate formal parameter %s with %s." (a.name.ToString()) (l.ToString())
            | MustReturnFirstClassType (p, n) -> p, sprintf "%s must return a first class type." (string n)
            | NonFirstClassReturnStmt p -> p, "Return statement must return a first class type."
            | ValueMustBeOfValueType l -> l.Range, sprintf "The identifier %s must be of a first class type." (l.ToString())
            | ExpectedBoolConds (r1, r2) -> Range.unionRanges r1.Range r2.Range, sprintf "Expressions %s and %s must both be boolean." (r1.ToString()) (r2.ToString())
            | MustBeNumeric (t1, t2) -> Range.unionRanges t1.Range t2.Range, sprintf "Expressions %s and %s must be numeric." (t1.ToString()) (t2.ToString())
            | SameTypeRequired (r1, r2) -> Range.unionRanges r1.Range r2.Range, sprintf "Expressions %s and %s must be of the same type." (r1.ToString()) (r2.ToString())
            | SameArithmeticTypeRequired (e1, e2) -> Range.unionRanges e1.Range e2.Range, sprintf "Expressions %s and %s must be of the same arithmetic type." (e1.ToString()) (e2.ToString())
            | SameFirstTypeRequired (p, f1, f2) -> p, sprintf "Types %s and %s must be the same." ((ValueTypes f1).ToString()) ((ValueTypes f2).ToString())
            | NoComparisonAllowed (e1, e2) -> Range.unionRanges e1.Range e2.Range, sprintf "Expressions %s and %s are structured value typed data and may not be compared at runtime directly using '=='." (e1.ToString()) (e2.ToString())
            | IncomparableReturnTypes (p, f1, f2) -> p, sprintf "The code block may return values of type %s or %s which are incomparable." ((ValueTypes f1).ToString()) ((ValueTypes f2).ToString())
            | VoidSubprogCannotReturnValues p -> p, sprintf "The return statement may not have a value payload since the subprogram is declared as void. (It does not have a \"returns\" declaration.)"
            | VoidReturnStmtMustReturn (p, t) -> p, sprintf "The return statement must have a payload of type %s according to the declaration of the subprogram." (t.ToString())
            | MustReturnSomething (p, f) -> p, sprintf "The subprogram declares the return type %s. However no return statements were found." ((ValueTypes f).ToString())
            | ReturnTypeMismatch (p, f1, f2) -> p, sprintf "The subprogram returns a %s which does not match the declared return type %s." (f2.ToString()) ((ValueTypes f1).ToString())
            | ActCallMustExplicitlyIgnoreResult (p, n) -> p, sprintf "The call of %s must explicitly ignore the non-void return value." (string n)
            | MayOrMayNotReturn (p, f1, f2) -> p, sprintf "The subprogram possibly returns a %s on some execution paths (but not on all). However it must always return a %s." ((ValueTypes f2).ToString()) ((ValueTypes f1).ToString())
            | ValueStructContainsRef (name, refField) -> name.range, sprintf "The structure %s is value typed but contains the reference typed element %s." name.idToString refField.name.basicId
            | ValueArrayMustHaveValueType r -> r, "A value typed array must contain value typed elements."
            | TooManyInitialisers (r, i) -> r, sprintf "More than %d initialisers have been given." i
            // statements
            | ExternalsInFunction p -> p, "External variables cannot be defined inside functions."
            | SynchronousStatementInFunction p -> p, "Functions must not contain synchronous control flow statements (await, run, abort, cobegin, infinite repeat...end)."
            | ActivityHasInstantaneousPath (p, q) -> p, sprintf "Activity %s has an instantaneous control flow path. Please make sure there at least one await or run statement on every possible path." q.id
            
            // --- evaluation ---
            // literals
            | NumberLargerThanAnyInt (p, number) -> p, sprintf "Literal '%s' does not fit into any intX, bitsX or natX type." (string number)
            | NumberLargerThanAnyBits (p, number) -> p, sprintf "Literal '%s' does not fit into any bitsX or natX type." (string number)
            | NumberLargerThanAnyFloat (p, number) -> p, sprintf "Literal '%s' does not fit into any floatX type." (string number)
            | LiteralNotInType (expr, typ) ->
                expr.range, sprintf "Literal '%s' cannot be represented in type '%s'." (string expr)(string typ)
            | LiteralNotInLargestType (expr, typ) ->
                expr.range, sprintf "Literal '%s' cannot be represented in largest type '%s'." (string expr)(string typ)

            // array indexes and sizes
            | NegativeArrayIndex expr -> 
                expr.range, sprintf "Array index '%s' is less than '0'." (string expr) 
            | PositiveSizeExpected (r, expr) -> r, sprintf "A array size must be positive but '%s' was given." (string expr)
            | ArraySizeOverflowsWordsize (r, wordsize, expr) -> 
                r, sprintf "The machine dependent 'word-size=%s' cannot represent array size '%s'." (string wordsize.ToInt) (string expr)        // evaluation
            
            // shift amounts    
            | NegativeShiftAmount expr ->
                expr.range, sprintf "Shift amount '%s' is less than '0'." (string expr) 
            
            // cast and conversions
            | LiteralDoesNotHaveType (rng, literal, typ) ->
                rng, sprintf "Literal '%s' does not have type '%s'." (string literal) (string typ)
            | LiteralCastNotInType (rng, literal, typ) ->
                rng, sprintf "Literal '%s' cannot be represented in type '%s'." (string literal) (string typ)
            | LiteralCastNotNecessary (rng, literal, typ) ->
                rng, sprintf "No conversion necessary. Literal '%s' should use a type annotation." (string literal)

            // arithmetic
            | UnaryMinusOverFlow (p, expr) -> p, sprintf "Overflow due to unary minus operation '-' on value '%s'." (string expr)
            
            | ArithmeticOverFlow (rng, lexpr, rexpr) -> 
                rng, sprintf "Overflow in arithmetic operation"
            | DivideByZero (rng, expr) ->
                rng, sprintf "Division by zero"

            // bitwise operators
            | UnaryMinusOnBitsLiteral (p, expr) -> p, sprintf "Invalid unary minus '-' on bits literal '%s'." (string expr)
            | ComplementOnBitsLiteral (p, expr) -> p, sprintf "Invalid bitwise negation '~' on bits literal '%s'." (string expr)
            | BitwiseBinaryOperationOnAnyBits (rng, lexpr, rexpr) ->
                rng, sprintf "Cannot resolve overloaded operation on unsized bits literals '%s' and '%s'." (string lexpr) (string rexpr)
    
            | ShiftOperationOnAnyBits (rng, expr) ->
                rng, sprintf "Cannot resolve overloaded shift operation on unsized bits literal '%s'." (string expr)
            
                    
            // --- attributes ---
            // annotations
            | UnsupportedAnnotation p -> p, "Unsupported annotation."
            | MissingAnnotation (p, key) -> p, sprintf "Missing annotation @[%s(...)]." key
            | MultipleUniqueAnnotation (second = p) -> p, sprintf "Unique annotation must not be specified multiply."
            | MissingNamedArgument (p, key) -> p, sprintf "Missing [... %s = \"<file>\" ...] annotation argument." key
            | MissingEntryPoint p -> p, "Blech program file must contain an activity with '@[EntryPoint]' annotation."
            | MultipleEntryPoints (second = p) -> p, "'@[EntryPoint]' activity already defined."
            | IllegalEntryPoint (p, pack) -> p, sprintf "Illegal '@[EntryPoint]' annotation in Blech libary '%s'." (String.concat "." pack.moduleName)
            // pragmas
            | UnknownPragma p -> p, "Unknown pragma."
            
            // | Dummy (p, msg) -> p, msg
 
            |> (fun (srcPos, msg) -> 
                { range = srcPos
                  message = msg }
                )

        member err.ContextInformation = 
            match err with
           
            // simple types
            | ExpectedBoolExpr (rng, _) -> 
                [ { range = rng; message = "condition expected"; isPrimary = true}]
            | ExpectedBitsExpr expr -> 
                [ { range = expr.range; message = "bits type expected"; isPrimary = true}]
            | UnaryMinusOnNatExpr (rng, _) -> 
                [ { range = rng; message = "must not be a nat type"; isPrimary = true}]
            | ExpectedInvertableNumberExpr (rng, _) -> 
                [ { range = rng; message = "number expected"; isPrimary = true}]
            
            // Type annotation and cast
            | WrongTypeAnnotation (rng, expr, typ)-> 
                [ { range = rng; message = "wrong type annotated"; isPrimary = true} 
                  { range = expr.range; message = sprintf "has type '%s'" (string expr.typ); isPrimary = false } ]
            | DownCast (rng, expr, typ) ->
                [ { range = rng; message = "no downcast allowed"; isPrimary = true }
                  { range = expr.range; message = sprintf "has type '%s'" (string expr.typ); isPrimary = false } ]
            | ImpossibleCast (rng, expr, typ) ->
                [ { range = rng; message = "cast not allowed"; isPrimary = true }
                  { range = expr.range; message = sprintf "has type '%s'" (string expr.typ); isPrimary = false } ]

            // Shift amounts, arrays sizes and indexes
            | NoShiftAmountType expr ->
                [ { range = expr.range; message = "number expected"; isPrimary = true } ]
            
            // bitwise operators
            | BitwiseOperationTypeMismatch (rng, lexpr, rexpr) ->
                [ { range = rng; message = "same bitsX arguments expected"; isPrimary = true}
                  { range = lexpr.range; message = sprintf "has type '%s'" (string lexpr.typ); isPrimary = false } 
                  { range = rexpr.range; message = sprintf "has type '%s'" (string rexpr.typ); isPrimary = false } ]
                
            | ExpectedBitsArguments (rng, lexpr, rexpr) ->
                [ { range = rng; message = "bitsX arguments expected"; isPrimary = true}
                  { range = lexpr.range; message = sprintf "has type '%s'" (string lexpr.typ); isPrimary = false } 
                  { range = rexpr.range; message = sprintf "has type '%s'" (string rexpr.typ); isPrimary = false } ]
                

            // --- evaluation ---
            
            // literals
            | NumberLargerThanAnyInt (rng, _)
            | NumberLargerThanAnyBits (rng, _) 
            | NumberLargerThanAnyFloat (rng, _) ->
                [ { range = rng; message = "oversized literal"; isPrimary = true}]
            
            | LiteralNotInLargestType (expr, _)
            | LiteralNotInType (expr, _) ->
                [ { range = expr.range; message = "cannot be represented"; isPrimary = true}]
                
            // array sizes and indexes
            | NegativeArrayIndex expr ->
                [ { range = expr.range; message = "non-negative index expected"; isPrimary = true} ]
            | PositiveSizeExpected (rng, _) ->
                [ { range = rng; message = "positive size expected"; isPrimary = true} ]
            | ArraySizeOverflowsWordsize (rng, wordsize, _) ->
                [ { range = rng; message = sprintf "'word-size=%s' overflow" (string wordsize.ToInt); isPrimary = true} ]
            
            // shift amounts
            | NegativeShiftAmount expr ->
                [ { range = expr.range; message = "non-negative shift amount expected"; isPrimary = true} ]
            
            // cast and conversions
            | LiteralDoesNotHaveType (rng, literal, typ) ->
                [ { range = rng; message = "type annotatin not possible "; isPrimary = true } 
                  { range = literal.range; message = sprintf "value does not have type '%s'" (string typ); isPrimary = false } ]
            | LiteralCastNotInType (rng, literal, typ) ->
                [ { range = rng; message = "conversion not possible "; isPrimary = true } 
                  { range = literal.range; message = sprintf "value not in '%s'" (string typ); isPrimary = false } ]
            | LiteralCastNotNecessary (rng, literal, typ) ->
                [ { range = rng; message = "no conversion necessary"; isPrimary = true } ]
                
            // arithmetic
            
            | UnaryMinusOnBitsLiteral (_, expr) 
            | ComplementOnBitsLiteral (_, expr) ->
                [ { range = expr.range; message = "unknown bits size"; isPrimary = true}]
            | UnaryMinusOverFlow (rng, expr) ->
                [ { range = rng; message = sprintf "unary minus overflow"; isPrimary = true}
                  { range = expr.range; message = sprintf "value is '%s'" (string expr); isPrimary = false} ]
            
            | ArithmeticOverFlow (rng, lexpr, rexpr) -> 
                [ { range = rng; message = sprintf "arithmetic overflow"; isPrimary = true}
                  { range = lexpr.range; message = sprintf "value is '%s'" (string lexpr) ; isPrimary = false}
                  { range = rexpr.range; message = sprintf "value is '%s'" (string rexpr) ; isPrimary = false} ]
            
            | DivideByZero (rng, expr) -> 
                [ { range = rng; message = sprintf "division by zero"; isPrimary = true}
                  { range = expr.range; message = sprintf "value is '%s'" (string expr) ; isPrimary = false} ]
                

            // bitwise
            | ShiftOperationOnAnyBits (rng, _)
            | BitwiseBinaryOperationOnAnyBits (rng, _, _) ->
                [ { range = rng; message = sprintf "overloading not resolved"; isPrimary = true} ]
            
            

            // --- annotations ---

            | UnsupportedAnnotation range -> 
                [ { range = range; message = "not supported"; isPrimary = true} ]
            | MissingAnnotation (range, key) -> 
                [ { range = range; message = sprintf "requires '%s' annotation" key; isPrimary = true} ]
            | MissingNamedArgument (range, key) ->
                [ { range = range; message = sprintf "requires '%s' argument" key; isPrimary = true} ]
            | MultipleEntryPoints (first, second) -> 
                [ { range = first; message = "definition"; isPrimary = false} 
                  { range = second; message = "redefinition"; isPrimary = true } ]
            | UnknownPragma range -> 
                [ { range = range; message = "not known"; isPrimary = true} ]
            | _ ->
                []

        member err.NoteInformation = 
            match err with
            // simple types
            | UnaryMinusOnNatExpr _ -> 
                [ "A nat type can only represent natural numbers." ]
            | ExpectedInvertableNumberExpr _ -> 
                [ "All numbers, with the exception of type nat, can be inverted."]
            
            // Type annotation and cast
            | WrongTypeAnnotation (_, _, typ)-> 
                [ sprintf "For changing the type use a cast 'as %s'" (string typ)]
            | ImpossibleCast (rng, expr, typ) ->
                [ "Type conversion is only allowed on simple types with no loss of information."
                  "NatX and bitsX types can be casted precisely to a bigger intX type."
                  "NatX, bitsX and intX types can be casted precisely to a bigger floatX type." ]
                  

            // Shift amounts, arrays sizes and indexes
            | NoShiftAmountType _ ->
                [ "A shift amount type it either intX, bitsX or natX."
                  "A shift amount must be greater than 0." 
                  "A shift amount is taken modulo the bitsize of the shifted value." ]                    
            
            // bitwise operators
            | BitwiseOperationTypeMismatch (rng, lexpr, rexpr) ->
                [ "Bitwise operators require arguments of the same bitsX type." 
                  "You can use a type cast 'as bitsX' to adopt the arguments." ]
                        
            | ExpectedBitsArguments _ ->
                [ "Bitwise operators are only defined for arguments of type bitsX."]
            

            // --- evaluation ---

            // type annotation and conversion 
            | LiteralCastNotNecessary (rng, literal, typ) ->
                [ sprintf "Use a type annotation '%s : %s'." (string literal) (string typ) ]
            
            // array indexes
            | PositiveSizeExpected _ ->
                [ sprintf "The number of array elements must be strictly positive." ]                    
            | NegativeArrayIndex _ ->
                [ sprintf "An array index must be greater than '0'." ]                    
            | ArraySizeOverflowsWordsize (_, wordsize, _) ->
                [ sprintf "The compiler option '--word-size=%s' defines the machine dependent word size." (string wordsize.ToInt) 
                  "See 'blechc --help'."]
            // arithmetic
            | UnaryMinusOnBitsLiteral _ -> 
                [ "Use a type annotation to define the size of the bits literal, e.g. '-(0x1: bits8)'." ]
            | ComplementOnBitsLiteral _ -> 
                [ "Use a type annotation to define the size of the bits literal, e.g. '~(0x1: bits8)'." ]
            | UnaryMinusOverFlow _  ->
                [ "Unary minus of an int value or a float value can overflow, e.g. - (-128: int8)." ]
            // bitwise
            | ShiftOperationOnAnyBits (_, expr) ->
                [ sprintf "Use a type annotation to define the size of the bits literal, e.g. '(%s: bits32)'." (string expr) ]    
            | BitwiseBinaryOperationOnAnyBits (_, expr, _) ->
                [ sprintf "Use a type annotation to define the size of one bits literal, e.g. '(%s: bits32)'." (string expr) ]
            
            | NegativeShiftAmount _ ->
                [ "An shift amount must be greater than '0'."
                  "A shift amount is taken modulo the bitsize of the shifted valued."]                    
            
            // annotations
            | UnsupportedAnnotation _ ->
                ["This Blech attribute is not supported here, check the spelling."]
            | MultipleEntryPoints _ -> 
                ["Delete one of the annotations."]
            | UnknownPragma _ ->
                ["This is not a defined Blech pragma attribute, check the spelling."]
            | _ ->
                []

//=============================================================================
// Result type
//=============================================================================
type TyChecked<'a> = Result<'a, TyCheckError list>

//=============================================================================
// Functions for TyChecked result type
//=============================================================================
module TyChecked =
    /// Zips a pair of Oks into an Ok of pairs
    /// In case at least one of the argument contains the Error case,
    /// simply concatenates the errors.
    let internal combine tyc1 tyc2 =
        match tyc1, tyc2 with
        | Error e1, Error e2 -> Error (e1 @ e2)
        | Error e1, _ -> Error e1
        | _, Error e2 -> Error e2
        | Ok o1, Ok o2 -> Ok (o1, o2)

    /// Similar to combine, except that it works on a list
    /// and returns an Ok of a list in the good case.
    let internal contract tycList =
        let rec recContract tycs res =
            match tycs with
            | [] -> res
            | x::xs ->
                match x, res with
                | Error e1, Error errs -> recContract xs <| Error (errs @ e1)
                | _, Error errs -> recContract xs <| Error errs
                | Error e1, _ -> recContract xs <| Error e1
                | Ok sth, Ok someList -> recContract xs (Ok (someList @ [sth])) // respect the order!
        recContract tycList (Ok [])

    /// Similar to contract, except that it works on an optional
    /// and returns an Ok of an optional in the good case
    let internal ofOption = function
        | None -> Ok None
        | Some res -> res |> Result.map Some

//=========================================================================
// Some debug helpers
//=========================================================================

    let internal debugShow msg v =
        printfn "%s: %A" msg v
        v
