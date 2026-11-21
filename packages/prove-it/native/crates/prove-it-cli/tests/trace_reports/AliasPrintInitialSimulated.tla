---- MODULE AliasPrintInitialSimulated ----
EXTENDS Naturals, TLC
VARIABLES x, y
Init == x = 0 /\ y = 0 /\ PrintT(<<"init", x>>)
Next == x < 3 /\ x' = x + 1 /\ y' = y
Inv == PrintT(<<"inv", x>>) /\ x > 0
Al == [x |-> x, p |-> PrintT(<<"alias", x>>)]
====
