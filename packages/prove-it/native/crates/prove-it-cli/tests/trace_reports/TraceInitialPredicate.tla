---- MODULE TraceInitialPredicate ----
EXTENDS Naturals, Sequences, TLCExt
VARIABLES y, x
Init == x = 0 /\ y = "a"
Next == x' = x + 1 /\ y' = y
Positive == x > 0
Alias == [x |-> x, trace |-> Trace]
====
