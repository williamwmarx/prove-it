---- MODULE AliasVariable ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 1 /\ x' = x + 1
Inv == x < 1
====
