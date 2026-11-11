---- MODULE TraceInInvariant ----
EXTENDS Naturals, Sequences, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == Len(Trace) < 3
====
