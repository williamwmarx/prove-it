---- MODULE RLetInstanceNamed ----
Op ==
  LET
    I == INSTANCE RecursiveHelper
    RECURSIVE I, K
  IN 0
====
