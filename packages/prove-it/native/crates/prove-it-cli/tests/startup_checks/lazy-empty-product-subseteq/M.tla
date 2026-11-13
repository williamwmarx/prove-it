---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = ((Int \X {}) \subseteq {})
Next == x' = x
====
