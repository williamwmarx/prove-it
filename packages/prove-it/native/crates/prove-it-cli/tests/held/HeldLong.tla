---- MODULE HeldLong ----
EXTENDS Naturals
VARIABLES odd, run
Init == odd = {} /\ run = {}
Next == /\ \E n \in 0..299 : n \notin run /\ (n = 0 \/ n - 1 \in run) /\ run' = run \cup {n}
        /\ odd' = odd \cup {2 * i + 1 : i \in run'}
Inv == /\ \A n \in run : 2 * n + 1 \in odd /\ 2 * n \notin odd
       /\ 300 \notin run
====
