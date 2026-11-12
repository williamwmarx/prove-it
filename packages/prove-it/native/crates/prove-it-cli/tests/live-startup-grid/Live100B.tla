---- MODULE Live100B ----
EXTENDS Naturals
CONSTANT N
VARIABLE x
Q == \A i \in {N} : [](x # i)
QS == \A i \in {j \in 0..3 : j = N} : [](x # i)
QE == \A i \in {N} : \E j \in {N} : [](x # j)
QK == \A i \in {1} : [](x # N)
====
