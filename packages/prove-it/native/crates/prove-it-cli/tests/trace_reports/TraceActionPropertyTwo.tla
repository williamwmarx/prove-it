---- MODULE TraceActionPropertyTwo ----
EXTENDS Naturals, Sequences, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x + 1
Small == [][x' < 1]_x
Alias == [x |-> x, length |-> Len(Trace)]
====
