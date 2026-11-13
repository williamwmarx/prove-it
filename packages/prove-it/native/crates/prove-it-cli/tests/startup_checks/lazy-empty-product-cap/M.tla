---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = ((Int \X {}) \cap {"a"})
Next == x' = x
====
