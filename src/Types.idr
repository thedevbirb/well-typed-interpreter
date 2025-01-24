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
  ||| A [Context] is a type alias that represents a vector of the types of
  ||| variables currently available in scope. The length of the vector
  ||| corresponds to the number of variables in scope.
  |||
  ||| Note that in this language only lambda expressions can introduce
  ||| new variable in scope.
  |||
  ||| Variables have a nameless representation, and they're "de Bruijn" 0-indexed
  ||| (reference: https://en.wikipedia.org/wiki/De_Bruijn_index).
  ||| An index indicates the number of lambdas between definition and use.
  ||| For example, in the expression `\x. \y. x y` the variable `x` has index 1
  ||| while `y` has 0.
  Context : Nat -> Type
  Context n = Vect n BirbType

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
  data Expression : Context n -> BirbType -> Type where
    ||| A [Value] takes an Idris2 integer and returns an expression
    ||| that evaluates to a [BirbInt].
    Value : Integer -> Expression context BirbInt
    ||| A [Variable] takes a proof that a certain variable in the context
    ||| has type `t` and returns an expression that evalues to a `t`.
    |||
    ||| Example:
    ||| ```idris2
    ||| proof_of_type : HasType (FS FZ) [BirbInt, BirbBool] BirbBool
    ||| proof_of_type = Next First
    |||
    ||| var : Expression [BirbInt, BirbBool] BirbBool
    ||| var = Variable proof_of_type
    ||| ```
    Variable : HasType i context t -> Expression context t
    ||| A [Lambda] is an expression that evalues to a function `Birb x t`.
    ||| The input corresponds to the body of the function, which is an expression
    ||| with a variable `x` in scope, added to the context, and that evalues to a type `t`.
    |||
    ||| It abstracts a construction like `\x -> ...)`.
    |||
    ||| Example:
    ||| ```idris2
    ||| -- A lambda function that takes a parameter of type `BirbInt` but always returns 0
    ||| lambda : Expression [] (BirbFun BirbInt BirbBool)
    ||| lambda = Lambda (Value 0)
    ||| ```
    Lambda : Expression (x :: context) t -> Expression context (BirbFun x t)


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
