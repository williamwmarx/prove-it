---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
P(m, v) == IF PrintT(m) THEN v ELSE v
Test == LET f(z) == P(z, z) IN f(1) + f(1) = 2
ASSUME Test
Init == x = 0
Next == LET g(z) == PrintT(<<"next", z>>) IN x < 2 /\ g(x) /\ x' = x + 1 /\ g(x')
Inv == LET h(z) == PrintT(<<"inv", z>>) IN h(x) /\ h(x)
====
