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
  Context : Nat -> Type
  Context n = Vect n BirbType
