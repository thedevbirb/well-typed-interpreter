module Examples

import Interpreter

-- Corresponds to the closure \x. \y. x + y. It an expression
-- which evalues to a function that takes a `BirbInt`
-- and returns a function that takes a `BirbInt` and returns a `BirbInt`.
add : Expression context (BirbFun BirbInt (BirbFun BirbInt BirbInt))
add = Lambda (Lambda (Op (+) (Variable First) (Variable (Next First))))

public export
result : Integer
result = (interpret Interpreter.Nil (App add (Value 1))) 2

