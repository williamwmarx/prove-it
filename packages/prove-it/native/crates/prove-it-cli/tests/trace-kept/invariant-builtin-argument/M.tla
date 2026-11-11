---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
Apply(F(_)) == {n \in Nat : n > F("level")}
D == <<[i \in {3, 1, 2} |-> i], Apply(TLCGet)>>

Init == x = 0
Next == x' = x + 1
Inv == x < 1 \/ D[1]["a"] = 1
====
