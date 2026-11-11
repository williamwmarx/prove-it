---- MODULE Live088B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
Op(a) == {1}
CI == INSTANCE Live088C WITH K <- 1
Q == LET S == {N} IN \A i \in S : [](x # 5)
====
