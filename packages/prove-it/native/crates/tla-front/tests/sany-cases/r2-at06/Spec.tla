---- MODULE Spec ----
A(G(_)) == 1
B == [[x \in {1} |-> 1] EXCEPT ![1] = A((@))]
====
