---- MODULE Spec ----
VARIABLE x
op == [y \in {1} |-> y]
B == op!(1)!1
C == op!(1)!2
====
