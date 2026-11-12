---- MODULE Spec ----
VARIABLE x
op == \E y : y = 1
B == op!(1)
C == op!(1, 2)
D == op!1
====
