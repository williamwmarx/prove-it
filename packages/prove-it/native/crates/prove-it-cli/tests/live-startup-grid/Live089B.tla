---- MODULE Live089B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
Op(a) == {1}
CI == INSTANCE Live089C WITH K <- 1
Q == \A i \in CI!S : [](x # 5)
====
