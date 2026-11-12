---- MODULE Live092B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
SN == {N}
SE == IF TRUE THEN {} ELSE {N}
Q == \A i \in (IF TRUE THEN {1} ELSE {N}) : [](x # 2)
====
