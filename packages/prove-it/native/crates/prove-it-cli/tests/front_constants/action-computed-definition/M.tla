---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT c
VARIABLE x
Init == x = 0
bb == c
cc == bb
B(p) == cc \/ x' = (x + p) % 3
Next == B(1)
====
