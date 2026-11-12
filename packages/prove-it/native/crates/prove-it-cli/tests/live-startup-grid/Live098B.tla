---- MODULE Live098B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
CI == INSTANCE Live098C WITH K <- 1
Q == LET S == {} \cap {N} IN \A i \in S : <>(x = i)
====
