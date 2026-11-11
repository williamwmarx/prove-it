---- MODULE M ----
EXTENDS Naturals
CONSTANT F(_)
J == INSTANCE I WITH H <- F
VARIABLE x
Init == x = J!Val
Next == x' = x
Inv == x = 5
====
