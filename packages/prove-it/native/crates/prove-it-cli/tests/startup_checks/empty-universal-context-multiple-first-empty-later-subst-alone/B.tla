---- MODULE B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N

Q == \A i \in {}, j \in {N} : <>(x=i+j)
====
