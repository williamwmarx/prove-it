---- MODULE Live094B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
CI == INSTANCE Live094C WITH K <- 1
DS == IF TRUE THEN {1} ELSE {N}
Q == \A i \in LET u == N IN {1} : [](x # 2)
====
