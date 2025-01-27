# About

This project is an implementation of a typed interpreter in Idris2 for a very
simple expression language called `BirbLang`, based on the notes of the [Idris2
crash course](https://idris2.readthedocs.io/en/latest/tutorial/interp.html).

Below is an example of a typed expression, along with its interpretation:

```idris
-- Corresponds to the closure \x. \y. x + y. It is an expression
-- which evalues to a function that takes a `BirbInt`
-- and returns a function that takes a `BirbInt` and returns a `BirbInt`.
add : Expression context (BirbFun BirbInt (BirbFun BirbInt BirbInt))
add = Lambda (Lambda (Op (+) (Variable First) (Variable (Next First))))

result : Integer
result = (interpret Interpreter.Nil (App add (Value 1))) 2
```

This simple interpreter showcases the crucial feature of the Idris2 language:
dependent types. In the example below, `Lambda` adds new variable of type
`BirbInt` in scope (the `context`), while `First`, `Next First` are constructor
for a type `HasType` that proves at compile time that the `i`-th variable in the
context of type `BirbInt`.

The two modules `Types` and `Interpreter`, other than providing the actual
implementation, strive to be a walkthrough of the making process and to uncover
all the (in my opinion) non-trivial details about it.

I hope this can be helpful for someone and my future self when I have to brush
up some concepts again :)
