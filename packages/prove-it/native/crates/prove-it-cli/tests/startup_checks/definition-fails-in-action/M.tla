---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
D == <<1, 2>>[3]
Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE x' = D
====
