---- MODULE TraceInvariantTool ----
EXTENDS Naturals, Sequences, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x < 3
Alias == [x |-> x, trace |-> Trace]
====
