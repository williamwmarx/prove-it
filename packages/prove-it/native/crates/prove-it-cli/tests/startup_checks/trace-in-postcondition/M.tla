---- MODULE M ----
EXTENDS TLCExt, TLC, Naturals, Sequences
VARIABLES b, A
Init == b = 0 /\ A = 1
Next == b' = (b + 1) % 3 /\ A' = A
Post == PrintT(Len(Trace))
====
