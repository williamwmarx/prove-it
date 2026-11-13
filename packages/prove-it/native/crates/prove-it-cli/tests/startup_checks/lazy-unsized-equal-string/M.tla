---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = ("a" = [Int -> {}])
Next == x' = x
====
