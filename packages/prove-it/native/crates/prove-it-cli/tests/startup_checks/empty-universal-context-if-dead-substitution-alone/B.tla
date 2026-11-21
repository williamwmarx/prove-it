---- MODULE B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
D == IF TRUE THEN {} ELSE {N}
Q == \A i \in D : <>(x=i)
====
