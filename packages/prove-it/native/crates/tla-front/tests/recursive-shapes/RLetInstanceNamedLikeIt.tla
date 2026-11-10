---- MODULE RLetInstanceNamedLikeIt ----
Op ==
  LET
    RECURSIVE I
    I == INSTANCE RecursiveHelper
  IN 0
====
