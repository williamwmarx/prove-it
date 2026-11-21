---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
D == [[a |-> 1] EXCEPT !.a = 2]
Inv == (D \in {D}) /\ (x = 1 => 1 \div 0 = 1)
====
