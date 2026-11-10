---- MODULE RLetInfix ----
Op ==
  LET
    RECURSIVE _ ** _
    a ** b == a ** b
  IN 1 ** 2
====
