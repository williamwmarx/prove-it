---- MODULE TraceRebuiltCount ----
EXTENDS TLCExt, TLC, Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = TLCGet("distinct")
Inv == Len(Trace) > 0
====
