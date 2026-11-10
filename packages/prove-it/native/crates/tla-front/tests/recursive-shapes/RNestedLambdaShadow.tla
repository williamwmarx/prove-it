---- MODULE RNestedLambdaShadow ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      Ap(Op(_)) == Op(0)
      F(n) == Ap(LAMBDA F : F)
    IN 0
  IN Outer
====
