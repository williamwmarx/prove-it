---- MODULE AliasDefinitionConstantTool ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x < 2
Constant == {1, 2} \X {"a"}
====
