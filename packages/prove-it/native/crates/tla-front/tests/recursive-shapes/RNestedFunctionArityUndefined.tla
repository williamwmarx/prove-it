---- MODULE RNestedFunctionArityUndefined ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_), K
      F[x \in {}] == 0
    IN 0
  IN Outer
====
