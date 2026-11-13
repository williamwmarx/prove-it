---- MODULE M ----
EXTENDS Naturals, Sequences
VARIABLES x, y
V == <<x, y>> \o <<x>>
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(V!1)
====
