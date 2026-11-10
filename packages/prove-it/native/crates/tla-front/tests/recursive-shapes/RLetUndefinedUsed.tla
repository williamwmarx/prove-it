---- MODULE RLetUndefinedUsed ----
Op ==
  LET
    RECURSIVE F(_)
  IN F({})
====
