---- MODULE LetBeforeRecursiveSection ----
VARIABLE x
Init == x = 0
Next == x' = x
P == LET A == TRUE RECURSIVE R R == []TRUE IN A
ASSUME P
====
