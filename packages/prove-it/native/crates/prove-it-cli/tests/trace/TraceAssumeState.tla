---- MODULE TraceAssumeState ----
EXTENDS TLCExt, TLC, Naturals
VARIABLES y, x
ASSUME Trace # <<>>
Init == x = 0 /\ y = 0
Next == UNCHANGED <<x, y>>
====
