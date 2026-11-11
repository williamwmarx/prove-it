---- MODULE AliasDefinitionFails ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 1 /\ x' = x + 1
Fails == [c |-> 1 \div 0]
====
