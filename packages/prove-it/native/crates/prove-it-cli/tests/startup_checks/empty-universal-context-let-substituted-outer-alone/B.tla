---- MODULE B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N

Q == LET S == {N} IN \A i \in S : \A j \in {} : <>(x=j)
====
