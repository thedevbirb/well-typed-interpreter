module Interpreter

data Expr = Val Int | Add Expr Expr | Mul Expr Expr

x : Expr
x = Val 1
