---- MODULE TraceDeadlock ----
EXTENDS Naturals, Sequences, TLCExt
VARIABLES y, x
Init == x = 0 /\ y = <<>>
Next == x < 2 /\ x' = x + 1 /\ y' = Append(y, x)
Alias == [x |-> x, trace |-> Trace]
====
