---- MODULE M ----
EXTENDS TLC, Sequences, Naturals
VARIABLE x
I == INSTANCE fy
Init == x = (I!Q(3) = 2)
Next == UNCHANGED x
====
