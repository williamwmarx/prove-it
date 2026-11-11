---- MODULE PostconditionString ----
EXTENDS Naturals, TLC, TLCExt, FiniteSets
VARIABLE x
Init == x = 0
Next == x' = IF x < 2 THEN x + 1 ELSE x
Inv == x < 2
P == "a"
====
