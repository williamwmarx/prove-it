---- MODULE B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N

Q == LET S == {} \cap {N} IN \A i \in S : <>(x=i)
====
