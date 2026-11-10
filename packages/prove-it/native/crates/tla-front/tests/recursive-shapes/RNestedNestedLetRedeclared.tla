---- MODULE RNestedNestedLetRedeclared ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(n) == LET RECURSIVE F(_) F(m) == 0 IN 0
    IN 0
  IN Outer
====
