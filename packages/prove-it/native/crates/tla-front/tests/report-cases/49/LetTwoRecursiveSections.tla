---- MODULE LetTwoRecursiveSections ----
VARIABLE x
Init == x = 0
Next == x' = x
P == LET RECURSIVE R R == []TRUE B == R RECURSIVE S S == TRUE C == S IN C
ASSUME P
====
