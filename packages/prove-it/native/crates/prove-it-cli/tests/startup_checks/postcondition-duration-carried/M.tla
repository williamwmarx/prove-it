---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2
Spec == Init /\ [][Next]_x
d == TLCGet("stats").duration
Post == /\ \A n \in {d} : n >= 0
        /\ DOMAIN [i \in {d} |-> i] # {}
        /\ LET f(n) == d + n IN f(0) >= 0
        /\ d = 7 \/ TRUE
====
