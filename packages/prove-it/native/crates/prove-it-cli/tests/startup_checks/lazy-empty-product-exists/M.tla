---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = (\E t \in (Int \X {}) : TRUE)
Next == x' = x
====
