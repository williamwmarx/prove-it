---- MODULE Spec ----
VARIABLE x
B == \A i \in {x'} : [](i = 1)
C == \E i \in {[](x=1)} : TRUE
====
