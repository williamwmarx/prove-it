---- MODULE RLetFunctionArityUndefined ----
Op ==
  LET
    RECURSIVE F(_), K
    F[x \in {}] == 0
  IN 0
====
