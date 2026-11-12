---- MODULE Spec ----
VARIABLE x
B == [i \in {x'} |-> [](x=1)]
C == [i \in {1}, j \in {[](x=1)} |-> 1]
====

