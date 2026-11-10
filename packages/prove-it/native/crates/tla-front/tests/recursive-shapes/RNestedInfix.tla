---- MODULE RNestedInfix ----
Op ==
  LET Outer ==
    LET
      RECURSIVE _ ** _
      a ** b == a ** b
    IN 1 ** 2
  IN Outer
====
