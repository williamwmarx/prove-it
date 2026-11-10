---- MODULE RNestedFunctionArity ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F[x \in {}] == 0
    IN 0
  IN Outer
====
