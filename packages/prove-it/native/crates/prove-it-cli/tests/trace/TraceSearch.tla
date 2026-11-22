---- MODULE TraceSearch ----
EXTENDS TLCExt, TLC, Naturals, Sequences
VARIABLES a, b
Init == a \in 1..2 /\ b \in 1..2
Next == \E i \in 1..2 : a' = (a + i) % 3 /\ b' = (b * i + Len(Trace)) % 3
Inv == PrintT(<<"inv", a, b, Trace>>)
Con == Len(Trace) < 3 /\ PrintT(<<"con", Len(Trace)>>)
Act == PrintT(<<"act", a, a', Trace>>)
====
