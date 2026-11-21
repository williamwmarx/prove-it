---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT c
VARIABLE x
Init == x = 0
B(p) == c \/ x' = (x + p) % 3
Next == B(1)
====
