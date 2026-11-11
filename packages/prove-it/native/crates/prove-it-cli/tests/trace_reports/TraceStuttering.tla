---- MODULE TraceStuttering ----
EXTENDS Naturals, Sequences, TLCExt
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Never == <>(x = 5)
Alias == [x |-> x, length |-> Len(Trace), trace |-> Trace]
====
