---- MODULE M ----
EXTENDS Naturals, TLC
Drawn == RandomElement(1..1000000)
Shown == Print("shown", 7)
ASSUME PrintT(<<"assumed", Drawn, Shown>>)
VARIABLES n, d
Init == n = 0 /\ d = Drawn
Next == \/ n = 0 /\ n' \in 1..4000 /\ d' = d
        \/ n \in 1..4000 /\ n' = n + 4000 /\ d' = Drawn + Shown
Inv == d >= Drawn
====
