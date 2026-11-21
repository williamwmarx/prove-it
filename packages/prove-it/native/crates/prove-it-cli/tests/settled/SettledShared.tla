---- MODULE SettledShared ----
EXTENDS Naturals
VARIABLE x
RECURSIVE H(_)
H(n) == IF n = 0 THEN {1} ELSE H(n - 1)
A == [a : H(1800)]
B == [a : A]
RECURSIVE F(_)
F(n) == IF n = 0 THEN FALSE
        ELSE IF n = 1800 THEN ([z |-> n] \in [a : A, b : B]) \/ F(n - 1)
        ELSE ([z |-> n] \in B) \/ F(n - 1)
Init == x = 0
Next == x' = x
Inv == F(1800) = FALSE
====
