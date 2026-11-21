---- MODULE M ----
EXTENDS _Possible, TLC, Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 6
Inv == _Track(x = 1, "alpha") /\ _Track(x = 2, "beta") /\ _Track(x > 2, "zeta") /\ _Track(x < 4, "mu")
Post == _PrintCounts /\ _CheckName("beta") /\ _CheckName("never")
====
