---- MODULE AliasConstant ----
EXTENDS Naturals
CONSTANT c
VARIABLE x
Init == x = 0
Next == x < c /\ x' = x + 1
====
