---- MODULE SettledLet ----
EXTENDS Naturals
VARIABLE x
RECURSIVE H(_)
H(n) == IF n = 0 THEN {1} ELSE H(n - 1)
RECURSIVE F(_)
F(n) == IF n = 0 THEN FALSE ELSE ([b |-> n] \in [a : LET RECURSIVE G(_)
                                  G(k) == IF k = 0 THEN {1} ELSE G(k - 1)
                              IN  G(1800)]) \/ F(n - 1)
Init == x = 0
Next == x' = x
Inv == F(1800) = FALSE
====
