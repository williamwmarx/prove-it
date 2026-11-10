---- MODULE RLetFunctionArityUsed ----
Op ==
  LET
    RECURSIVE F(_)
    F[x \in {}] == 0
  IN F({})
====
