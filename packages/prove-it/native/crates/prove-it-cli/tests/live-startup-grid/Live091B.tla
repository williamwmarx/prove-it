---- MODULE Live091B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
SN == {N}
SE == IF TRUE THEN {} ELSE {N}
Q == LET S == {N} IN \A i \in S : [](x # 2)
====
