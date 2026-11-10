---- MODULE RLetNamedInBoundBefore ----
Op ==
  LET
    G[x \in F] == 0
    RECURSIVE F
    F == {}
  IN 0
====
