---- MODULE GeqInt ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME "a" >= 1
====
