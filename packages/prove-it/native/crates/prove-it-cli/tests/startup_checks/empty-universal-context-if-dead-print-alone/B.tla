---- MODULE B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
D == IF TRUE THEN {} ELSE Print("dead", {N})
Q == \A i \in D : <>(x=i)
====
