---- MODULE LetOp ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = 1-x
Inv == LET P(a) == (a = x) /\ (a = x) IN P(x)
====
