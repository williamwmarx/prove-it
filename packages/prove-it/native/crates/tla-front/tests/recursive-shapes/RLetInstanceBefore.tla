---- MODULE RLetInstanceBefore ----
Op ==
  LET
    I == INSTANCE RecursiveHelper
    RECURSIVE F(_)
    F(n) == I!H
  IN 0
====
