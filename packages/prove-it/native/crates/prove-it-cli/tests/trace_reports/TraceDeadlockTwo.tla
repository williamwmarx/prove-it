---- MODULE TraceDeadlockTwo ----
EXTENDS Naturals, Sequences, TLCExt
VARIABLE x
Init == x = 0
Next == x < 1 /\ x' = x + 1
Alias == [x |-> x, length |-> Len(Trace)]
====
