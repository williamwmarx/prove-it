---- MODULE HeldModel ----
EXTENDS Naturals
CONSTANT c
VARIABLE held
Init == held = {}
Next == \E n \in 1..13 : held' = held \cup {n}
Inv == c \notin held /\ \A n \in 1..13 : n \in held \/ n \notin held
====
