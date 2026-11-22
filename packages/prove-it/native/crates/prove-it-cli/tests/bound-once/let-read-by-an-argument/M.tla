---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLES x, q
G(a, b) == IF b THEN <<a, a>> ELSE <<>>
Init == x = 0 /\ q = << >>
Next == /\ x < 6
        /\ x' = x + 1
        /\ LET h == Head(q)
               r == G(h, x >= 3)
           IN q' = IF Len(r) = 2 /\ Len(r) < 5 THEN Tail(q) ELSE Append(q, x)
Inv == Len(q) < 4
====
