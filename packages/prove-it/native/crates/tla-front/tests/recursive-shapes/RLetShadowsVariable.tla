---- MODULE RLetShadowsVariable ----
VARIABLE F
Op ==
  LET
    RECURSIVE F(_)
    F(n) == 0
  IN F({})
====
