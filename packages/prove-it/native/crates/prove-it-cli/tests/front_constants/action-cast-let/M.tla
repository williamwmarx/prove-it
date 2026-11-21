---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT c
VARIABLE x
Init == x = 0
Next == LET q == c IN q \/ x' = (x + 1) % 3
====
