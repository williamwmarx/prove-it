---- MODULE TraceTwo ----
EXTENDS Naturals, Sequences, TLCExt
VARIABLES y, x
Init == x = 0 /\ y = "a"
Next == x' = x + 1 /\ y' = y
Inv == x < 1
Alias == [x |-> x, length |-> Len(Trace), trace |-> Trace]
====
