---- MODULE Counter ----
EXTENDS Naturals
VARIABLES x, y
Inc(v) == v + 1
Init == x = 0 /\ y \in 0..1
Step == /\ x < 1999
        /\ LET next == Inc(x) IN x' = next
        /\ UNCHANGED y
Flip == \/ y = 0 /\ y' = Inc(y) /\ UNCHANGED x
        \/ y = 1 /\ y' = 0 /\ UNCHANGED x
Next == Step \/ Flip
Small == x + y < 3000
Moving == x' >= x
Inv == x >= 0
====
