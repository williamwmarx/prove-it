---- MODULE B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N

Q == \A i \in {}, j \in (1 \div 0) : <>(x=i+j)
====
