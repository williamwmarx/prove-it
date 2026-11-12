---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT S
VARIABLE x
Ignore(a) == TRUE
Once(a) == a = 1
Ignore2(a) == Ignore(a) /\ Ignore(a)
C == LET L(a) == TRUE IN L(1 \div 0)
Init == x = 0
Next == x' = x
ASSUME C
====
