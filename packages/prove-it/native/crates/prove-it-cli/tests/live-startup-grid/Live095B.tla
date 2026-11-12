---- MODULE Live095B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
CI == INSTANCE Live095C WITH K <- 1
DS == IF TRUE THEN {1} ELSE {N}
Q == LET S == {N} IN \A i \in S : \A j \in {} : <>(x = j)
====
