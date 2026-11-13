---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = PrintT(Int \X {})
Next == x' = x
====
