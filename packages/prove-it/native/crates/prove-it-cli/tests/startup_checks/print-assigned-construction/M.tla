---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLES x, y
Init == x = 1..3 /\ y = {1, 2} /\ PrintT(<<x, y>>)
Next == x' = {3, 2, 1} /\ y' = 1..2 /\ PrintT(<<x', y'>>)
====
