module Interpreter

import Types
import Data.Vect

||| [Environment] is a type indexed by [Context], meaning that it carries
||| information of the types of the variables in scope, that can be created
||| by runtime Idris values by interpreting their type.
data Environment : Context n -> Type where
  Nil : Environment Nil
  ||| Extends the environment with a runtime value of the type
  ||| corresponding to the next [BirbType] in the context.
  |||
  ||| Example:
  ||| ```idris2
  ||| -- Since the type of `env` must be a result of using `::`,
  ||| -- `[BirbInt]` matches `(t :: context)` with `t == BirbInt`
  ||| -- which means `1` must be of type `interpretType t == Int`
  ||| -- which is correct
  ||| env : Environment [BirbInt]
  ||| env = 1 :: Nil
  ||| ```
  (::) : interpretType t -> Environment context -> Environment (t :: context)

||| [lookup] is a function that translates a [BirbType] in an [Enviroment]
||| to an Idris type. The definition reads clearly: if you have a proof
||| that the `i`-th variable in the context of the environment is of type
||| `t`, return its interpreted type.
lookup : HasType i context t -> Environment context -> interpretType t
-- Example:
-- ```idris2
-- env : Environment [BirbInt, BirbBool]
-- env = 1 :: True :: Nil
--
-- -- * `interpretType t` must match `Int`.
-- -- * `Environment [BirbInt, BirbBool]` matches `(x :: env_context)` 
-- --   with `x == interpretType BirbInt == Int`, so `t == BirbInt`.
-- -- * `env_context == Environment [BirbBint, BirbBool]`, so `context == [BirbInt, BirbBool]`
-- -- * `First` is able to produce `HasType FZ [BirbInt, BirbBool] BirbInt`.
-- val : Int
-- val = lookup First env
-- ```
lookup First (x :: env_context) = x
-- Recursive definition that relies of `First` as a base case.
lookup (Next k) (x :: env_context) = lookup k env_context
