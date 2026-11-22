---- MODULE TraceRebuilt ----
EXTENDS TLCExt, TLC, Naturals, Sequences
VARIABLE x
Init == x = 0
Next == PrintT(<<"step", x>>) /\ x' = (x + 1) % 4
Inv == Len(Trace) > 0
====
