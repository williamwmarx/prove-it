---- MODULE Live093B ----
EXTENDS Naturals, TLC
VARIABLE x
CI == INSTANCE Live093C WITH K <- 1
Q == \A i \in CI!S : [](x # 2)
====
