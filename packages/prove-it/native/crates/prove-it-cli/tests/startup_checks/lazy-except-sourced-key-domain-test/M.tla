---- MODULE M ----
EXTENDS Integers, TLC
S == {1, 2}
Test == LET f == [x \in S |-> x] IN PrintT([f EXCEPT ![{1}] = 5][1])
VARIABLE v
Init == v = TRUE
Next == UNCHANGED v
Inv == v /\ Test
====
