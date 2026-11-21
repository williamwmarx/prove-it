---- MODULE ExitInNext ----
EXTENDS Naturals, Sequences, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == \/ x' = x + 1 /\ TLCSet("exit", x = 1)
        \/ x' = x + 10 /\ PrintT(x)
====
