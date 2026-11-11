---- MODULE PostconditionConstantTool ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Never == 1 > 2
====
