---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLES x, y
Init == x = 1 /\ ({1} \cup {2}) /\ y = 1
Next == UNCHANGED <<x,y>>
====
