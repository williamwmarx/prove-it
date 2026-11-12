---- MODULE Live097B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
CI == INSTANCE Live097C WITH K <- 1
Q == \A i \in CI!E : <>(x = i)
====
