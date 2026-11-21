---- MODULE B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
D == IF TRUE THEN {} ELSE (1 \div 0)
Q == \A i \in D : <>(x=i)
====
