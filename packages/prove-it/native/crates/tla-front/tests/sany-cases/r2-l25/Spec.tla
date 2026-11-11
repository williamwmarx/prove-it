---- MODULE Spec ----
A == [[x \in {1} |-> 1] EXCEPT ![1] = 2]
B == A!1
C == A!2
D == A!3
====
