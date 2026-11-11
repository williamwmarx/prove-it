---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
F(e) == e /\ e
Post == /\ F(Print(<<"a", TLCGet("distinct")>>, TRUE))
        /\ LET v == Print(<<"b", TLCGet("stats").distinct>>, TRUE) IN v /\ v
        /\ F(Print("c", TRUE))
====
