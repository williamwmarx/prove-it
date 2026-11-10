---- MODULE RNestedNamedInBoundBefore ----
Op ==
  LET Outer ==
    LET
      G[x \in F] == 0
      RECURSIVE F
      F == {}
    IN 0
  IN Outer
====
