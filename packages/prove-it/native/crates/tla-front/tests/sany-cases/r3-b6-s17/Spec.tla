---- MODULE Spec ----
VARIABLE x
op == CHOOSE y : y = 1
B == op!(1)
C == op!1
D == op!(1)!1
====
