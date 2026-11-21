---- MODULE AliasPrintSimulated ----
EXTENDS Naturals, TLC
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x < 3 /\ x' = x + 1 /\ y' = y
Inv == x < 2
Al == [x |-> x, p |-> PrintT(<<"alias", x>>)]
====
