---- MODULE TraceLasso ----
EXTENDS Naturals, Sequences, TLCExt
VARIABLES y, x
Init == x = 0 /\ y = "a"
Next == /\ x' = IF x = 3 THEN 1 ELSE x + 1
        /\ y' = y
Spec == Init /\ [][Next]_<<x, y>> /\ WF_<<x, y>>(Next)
Never == <>(x = 5)
Alias == [x |-> x, length |-> Len(Trace), trace |-> Trace]
====
