---- MODULE RLetExtendsUndefined ----
EXTENDS RecursiveHelper
Op ==
  LET
    RECURSIVE F(_)
  IN 0
====
