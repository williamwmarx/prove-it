---- MODULE AliasDefinitionConstant ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 1 /\ x' = x + 1
Constant == [c |-> 1]
====
