---- MODULE TraceLassoLong ----
EXTENDS Naturals, Sequences, TLCExt
VARIABLES y, x
Init == x = 0 /\ y = "a"
Next == /\ x' = IF x = 3 THEN 2 ELSE x + 1
        /\ y' = y
Spec == Init /\ [][Next]_<<x, y>> /\ WF_<<x, y>>(Next)
Never == <>(x = 5)
Xs == [position \in DOMAIN Trace |-> Trace[position].x]
Alias == [x |-> x, xs |-> Xs, last |-> IF Trace = <<>> THEN "none" ELSE Trace[Len(Trace)]]
====
