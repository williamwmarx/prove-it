---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Ignore(a) == TRUE
Post == /\ Ignore(TLCGet("stats").duration)
        /\ TLCGet("stats") = TLCGet("stats")
        /\ LET f[i \in {TLCGet("stats").duration}] == i IN DOMAIN f # {}
====
