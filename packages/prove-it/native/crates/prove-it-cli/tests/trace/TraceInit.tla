---- MODULE TraceInit ----
EXTENDS TLCExt, TLC, Naturals, Sequences
VARIABLES p, q, r
Init == p = 0 /\ Len(Trace) = 0 /\ q = 0 /\ r = 0
Next == UNCHANGED <<p, q, r>>
====
