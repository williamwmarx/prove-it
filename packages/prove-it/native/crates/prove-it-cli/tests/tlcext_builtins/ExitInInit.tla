---- MODULE ExitInInit ----
EXTENDS Naturals, Sequences, TLC, TLCExt
VARIABLE x
Init == x \in {1, 2} /\ TLCSet("exit", x = 1)
Next == x' = x + 1
====
