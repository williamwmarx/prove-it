---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
D0 == TLCSet(1, TLCSet(1, 2)) \cup Print([y \in 1..3 |-> y], TRUE)
D1 == DOMAIN TLCSet(1, [y \in {"a", "b"} |-> ("a" :> 1)])
D2 == LET L == TLCSet(1, "a") IN PrintT(<<L, L>>)
D3 == (TLCSet(1, Cardinality(2)))[1] /\ PrintT(3)
Init == x = 0
Next == x < 1 /\ x' = x + 1
ASSUME PrintT(4) /\ D1 = {}
====
