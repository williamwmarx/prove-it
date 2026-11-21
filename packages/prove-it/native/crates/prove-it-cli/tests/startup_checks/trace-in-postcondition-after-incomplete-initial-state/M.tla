---- MODULE M ----
EXTENDS TLCExt, Naturals, Sequences
VARIABLES y, x, Z
Init == y = 0 /\ x = 1
Next == UNCHANGED <<y, x, Z>>
Post == Len(Trace) > 0
====
