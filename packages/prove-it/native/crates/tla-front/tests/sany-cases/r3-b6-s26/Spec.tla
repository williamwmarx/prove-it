---- MODULE Spec ----
VARIABLE x
op(a, b) == a + b
B == op!1
C == op(1, 2)!3
D == op(1)!1
====
