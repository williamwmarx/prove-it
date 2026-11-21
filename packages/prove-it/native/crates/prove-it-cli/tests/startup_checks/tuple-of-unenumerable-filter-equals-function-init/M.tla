---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE v
Init == v = 0 /\ <<{x \in 0 : TRUE}, 1>> = [x \in {1, 2} |-> x]
Next == v' = v
====
