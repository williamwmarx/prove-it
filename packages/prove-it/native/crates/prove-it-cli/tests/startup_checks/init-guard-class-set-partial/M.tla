---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLES x, y
S == {1}
F(i) == {i}
Init == x = 1 /\ ({1}) /\ y = 1
Next == UNCHANGED <<x,y>>
====
