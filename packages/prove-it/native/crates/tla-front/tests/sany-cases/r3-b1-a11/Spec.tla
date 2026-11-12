---- MODULE Spec ----
CONSTANT c
VARIABLE x
B == \EE y : c
C == \E y \in {x'} : [](y = 1)
D == CHOOSE y \in {x'} : [](y=1)
====
