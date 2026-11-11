---- MODULE AliasArgument ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 1
Next == x < 2 /\ x' = x + 1 /\ y' = y
Argument(n) == [n |-> n, x |-> x]
====
