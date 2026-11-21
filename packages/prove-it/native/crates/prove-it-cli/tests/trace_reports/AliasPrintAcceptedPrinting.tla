---- MODULE AliasPrintAcceptedPrinting ----
EXTENDS Naturals, TLC
VARIABLES x, y
Next == x < 2 /\ x' = x + 1 /\ y' = y /\ PrintT(<<"next", x>>)
Spec == x = 0 /\ y = 0 /\ [][Next]_<<x, y>>
P == [](x = 1 => [](x = 1))
Al == [x |-> x, p |-> PrintT(<<"alias", x>>)]
====
