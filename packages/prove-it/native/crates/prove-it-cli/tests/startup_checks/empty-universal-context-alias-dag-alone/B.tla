---- MODULE B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
E == {}
A == E
C == E
D == A \cup C
Q == \A i \in D : <>(x=i)
====
