---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = DOMAIN [a |-> (Int \X {}) \cap {"a"}]
Next == x' = x
====
