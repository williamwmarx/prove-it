---- MODULE M ----
EXTENDS Sequences
R(s) == 9
VARIABLE x
Init == x = 0
Next == x' = x
Inv == Len(<<1,2>>) = 9
====
