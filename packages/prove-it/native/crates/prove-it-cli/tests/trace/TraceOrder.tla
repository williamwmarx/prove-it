---- MODULE TraceOrder ----
EXTENDS TLCExt, TLC, Naturals, Sequences
VARIABLES y, x
Init == x = 0 /\ y = 1
Next == x' = (x + 1) % 2 /\ y' = y
Inv == PrintT(Trace)
====
