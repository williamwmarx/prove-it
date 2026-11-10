---- MODULE RNestedFunctionArityUsed ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F[x \in {}] == 0
    IN F({})
  IN Outer
====
