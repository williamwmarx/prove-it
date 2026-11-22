---- MODULE M ----
EXTENDS Aid, Naturals, TLC
VARIABLE s
Init == s = 0
Next == UNCHANGED s
Inv == IF FALSE THEN Make = 1 ELSE TRUE
====
