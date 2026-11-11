---- MODULE Spec ----
ZZ == 1 \star 2
A(F(_)) == 1
B == [[x \in {1} |-> 1] EXCEPT ![1] = A(@)]
====
