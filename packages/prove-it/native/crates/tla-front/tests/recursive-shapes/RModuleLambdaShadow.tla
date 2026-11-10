---- MODULE RModuleLambdaShadow ----
RECURSIVE F(_)
Ap(Op(_)) == Op(0)
F(n) == Ap(LAMBDA F : F)
====
