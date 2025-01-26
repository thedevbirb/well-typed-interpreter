module Interpreter

import public Types
import public Data.Vect

||| [Environment] is a type indexed by [Context], meaning that it carries
||| information of the types of the variables in scope, that can be created
||| by runtime Idris values by interpreting their type.
public export
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

||| An interpreter takes an environment with its context, an expression of type `t`
||| in BirbLang and returns its value of idris type `interpretType t`
public export
interpret : Environment context -> Expression context t -> interpretType t
-- Given the environment, a variable consists of a proof that a certain value
-- belongs to the context. As such, we look it up in the environment.
interpret env (Variable x) = lookup x env 
-- An `Integer` is simply returned
interpret env (Value x) = x
-- Since a `Lambda` is created with an expression that adds a new `x` in scope 
-- and that evalues to `t`, its interpretation is an Idris closure
-- where we interpret its scope expression and add the parameter to the environment.
-- Example:
-- ```idris2
-- result : Int
-- -- intrepted as \x => interpret (x :: Nil) (Value 0)
-- result = interpret Nil (Lambda Value 0)
-- ```
interpret env (Lambda expr) = \x => interpret (x :: env) expr
-- The intepretation of a function application is the applying
-- the interpreted argument to the interpreted function.
interpret env (App f x) = interpret env f (interpret env x)
-- Note that `op` here is already an Idris operator, so the interpretation
-- is the application of the operator to its interpreted arguments.
interpret env (Op op x y) = op (interpret env x) (interpret env y)
-- For the `If` case is a straightforward interpretation of the underlying expressions
interpret env (If expr_bool expr_then expr_else) =
  if (interpret env expr_bool)
    then (interpret env expr_then)
    else (interpret env expr_else)
