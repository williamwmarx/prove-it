---- MODULE RNestedFunctionBoundShadow ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(n) == [F \in {} |-> 0]
    IN 0
  IN Outer
====
