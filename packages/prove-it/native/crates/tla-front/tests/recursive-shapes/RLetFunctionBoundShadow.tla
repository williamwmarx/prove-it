---- MODULE RLetFunctionBoundShadow ----
Op ==
  LET
    RECURSIVE F(_)
    F(n) == [F \in {} |-> 0]
  IN 0
====
