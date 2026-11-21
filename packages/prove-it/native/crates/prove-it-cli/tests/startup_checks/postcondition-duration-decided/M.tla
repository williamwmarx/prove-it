---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Dur == TLCGet("stats").duration
Post ==
    LET d == TLCGet("stats").duration
        unused == TLCGet("duration")
    IN /\ d >= 0
       /\ PrintT(<<Dur \in Nat, 0 > d>>)
       /\ (FALSE /\ PrintT(d)) = FALSE
       /\ IF d < 0 THEN PrintT(d) ELSE TLCGet("stats").distinct = 1
====
