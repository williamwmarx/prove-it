---- MODULE AliasAssigned ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Inv == x < 2
Alias == [y |-> x]
====
