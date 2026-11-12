---- MODULE Spec ----
RECURSIVE foo(_)
bar == LET foo(a) == 1 IN foo(1)
foo(a) == 1
====
