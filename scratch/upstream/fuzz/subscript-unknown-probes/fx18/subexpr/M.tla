---- MODULE M ----
EXTENDS Naturals, Sequences
VARIABLES x, y
V == lab :: <<x, y>>
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(V!lab)
====
