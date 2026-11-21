---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Test == /\ PrintT([y \in 1..2 |-> {y} \cup {3}])
        /\ PrintT([y \in 1..2 |-> {y, 3} \cap {2, 3}])
        /\ PrintT([y \in 1..2 |-> (1..3) \ {y}])
        /\ PrintT([y \in 1..2 |-> {y + z : z \in 1..2}])
        /\ PrintT([y \in 1..2 |-> {1..z : z \in 1..y}])
        /\ PrintT([y \in 1..2 |-> UNION {{y}, {3}}])
        /\ PrintT([y \in 1..2 |-> {1..y} \cup {3..4}])
ASSUME Test
Init == x = 0
Next == x' = x
====
