---- MODULE RLetInstanceAfter ----
Op ==
  LET
    RECURSIVE F(_)
    I == INSTANCE RecursiveHelper
    F(n) == I!H
  IN 0
====
