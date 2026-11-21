---- MODULE B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N

Q == \A i \in {1} : \A j \in {} : <>(x=j)
====
