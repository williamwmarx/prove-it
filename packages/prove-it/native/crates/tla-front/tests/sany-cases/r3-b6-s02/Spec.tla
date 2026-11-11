---- MODULE Spec ----
VARIABLE x
op == \A i \in {1} : lab(i) :: i
B == op!lab(1)!1
C == op!lab(1)!2
D == op!labx
====
