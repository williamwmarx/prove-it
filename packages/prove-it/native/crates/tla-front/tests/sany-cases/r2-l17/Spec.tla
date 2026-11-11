---- MODULE Spec ----
A == \E x \in {1} : x
B == A!(1)
C == A!(1, 2)
D == A!1!(2)
====
