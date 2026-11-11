---- MODULE AliasUndefinedTool ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = "a"
Next == x < 1 /\ x' = x + 1 /\ y' = y
====
