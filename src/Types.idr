||| Defines the types of the Birb language and functions to work with them.
module Types

import Data.Vect

||| The types of the Birb language.
||| This data type represents the type system of the Birb language.
||| - `BirbInt` represents integer types.
||| - `BirbBool` represents boolean types.
||| - `BirbFun` represents a function type, where the first `BirbType` is the
|||    input type, and the second `BirbType` is the output type.
export
data BirbType : Type where
  BirbInt : BirbType
  BirbBool : BirbType
  BirbFun : BirbType -> BirbType -> BirbType

-- Alternatively, you could write the same type using a simpler syntax:
-- data BirbType = BirbInt | BirbBool | BirbFun BirbType BirbType


||| Interprets a Birb type into an Idris2 type.
||| - `BirbInt` is interpreted as the Idris2 `Int`.
||| - `BirbBool` is interpreted as the Idris2 `Bool`.
||| - `BirbFun a b` is interpreted as a function type in Idris2, where
|||    the input has type `a` and the output has type `b`.
export
interpretType : BirbType -> Type
interpretType BirbInt = Int
interpretType BirbBool = Bool
interpretType (BirbFun a b) = interpretType a -> interpretType b

-- NOTE: this mutual block isn't necessary but helps with clarity
mutual
  ||| Represents an expression in the Birb language.
  |||
  ||| Each expression is well-typed, ensuring that only valid programs can
  ||| be written in the Birb language. An expression may use variables from
  ||| the current [Context], which tracks the types of variables in scope.
  |||
  ||| The type `Expr` is polymorphic type that can be read as follows:
  ||| - It takes a [Context], representing the variables available in scope.
  ||| - It takes a `BirbType`, representing the type of the expression itself.
  ||| - It returns an Idris2 type, ensuring type safety at the language level.
  data Expression : Context n -> BirbType -> Type

  ||| A [Context] is a type alias that represents a vector of the types of
  ||| variables currently available in scope. The length of the vector
  ||| corresponds to the number of variables in scope.
  |||
  ||| Variables have a nameless representation, and they're "de Bruijn" 0-indexed
  ||| (reference: https://en.wikipedia.org/wiki/De_Bruijn_index).
  ||| An index indicates the number of lambdas between definition and use.
  ||| For example, in the expression `\x. \y. x y` the variable `x` has index 1
  ||| while `y` has 0.
  Context : Nat -> Type
  Context n = Vect n BirbType

  ||| [HasType] is a data type that encodes evidence (or proof) that
  ||| the `i`-th variable in the context is of the provided `BirbType`.
  data HasType : Fin n -> Context n -> BirbType -> Type where
    ||| [First] proves that the first variable at index `FZ` (the zeroth index)
    ||| in the context has the provided type `t`.
    ||| The constructor is essentially a pattern much of the structure of the type.
    |||
    ||| Example:
    ||| ```idris2
    ||| -- Correct usage: The zeroth variable has type `BirbInt`, which matches the proof.
    ||| proof1 : HasType FZ [BirbInt, BirbBool] BirbInt
    ||| proof1 = First
    ||| 
    ||| -- Incorrect usage: The type `BirbFun` doesn't match the first element `BirbInt`,
    ||| -- so this would result in a compile-time error.
    ||| -- proof2 : HasType FZ [BirbInt, BirbBool] BirbFun
    ||| -- proof2 = First
    ||| ```
    First : HasType FZ (t :: context) t
    ||| [Next] return a proof that the `k+1`-th variable in the context has type `t`
    ||| if you provide a proof that, in a shorter context with one less element,
    ||| the `k`-th variable has type `t`.
    |||
    ||| Example:
    ||| ```idris2
    ||| -- The context `[BirbInt, BirbBool]` implies two things:
    ||| -- 1. Since its length is 2, it must be `(FS k) == FS FZ` so `k == FZ`.
    ||| -- 2. Since it must match `(u :: context)`, it means that `context == [BirbBool]`
    ||| -- As such `Next` needs as argument a `HasType FZ [BirbBool] BirbBool` which
    ||| -- `First` is able to create.
    ||| proof2 : HasType (FS FZ) [BirbInt, BirbBool] BirbBool
    ||| proof2 = Next First
    ||| ```
    Next : HasType k context t -> HasType (FS k) (u :: context) t

