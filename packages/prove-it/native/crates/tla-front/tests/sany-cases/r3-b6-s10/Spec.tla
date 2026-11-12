---- MODULE Spec ----
VARIABLE x
op == [x EXCEPT ![1] = 2]
B == op!1
C == op!2
D == op!3
====
