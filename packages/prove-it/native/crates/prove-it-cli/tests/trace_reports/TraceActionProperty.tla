---- MODULE TraceActionProperty ----
EXTENDS Naturals, Sequences, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x + 1
Small == [][x' < 3]_x
Alias == [x |-> x, length |-> Len(Trace)]
====
