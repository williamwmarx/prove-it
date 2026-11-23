---- MODULE LetSectionInRecursiveOperator ----
VARIABLE x
Init == x = 0
Next == x' = x
RECURSIVE F(_)
F(n) == LET A == TRUE RECURSIVE R R == []TRUE IN A
ASSUME F(1)
====
