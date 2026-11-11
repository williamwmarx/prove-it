---- MODULE Live096B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N, F(_)
Q == <>N
Q2 == <>(N + 0)
QF == <>F(1)
QA == \A i \in {N} : <>(x = i)
QA2 == \A i \in {1} : <>(x = i)
QA3 == \A i \in {1} : [](x # 2)
QA4 == \A i \in {N} : [](x # 2)
QA5 == \A i \in {F(1)} : [](x # 2)
QA6 == \A i \in {} : [](x # N)
QE == \E i \in {N} : <>(x = i)
QL == LET S == {1} IN \A i \in S : [](x # 2)
====
