---- MODULE Live099B ----
EXTENDS Naturals, TLC
VARIABLE x
CONSTANT N
CI == INSTANCE Live099C WITH K <- 1
Q == \A i \in (IF TRUE THEN {} ELSE {N}) : <>(x = i)
====
