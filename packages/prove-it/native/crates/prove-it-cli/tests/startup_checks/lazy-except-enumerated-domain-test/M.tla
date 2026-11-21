---- MODULE M ----
EXTENDS Integers, TLC
Test == LET f == [x \in {1, 2} |-> x] IN PrintT([f EXCEPT ![{1}] = 5][1])
VARIABLE v
Init == v = TRUE
Next == UNCHANGED v
Inv == v /\ Test
====
