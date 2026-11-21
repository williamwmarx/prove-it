---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
Same == DOMAIN [m \in Nat, k \in {1} |-> m] = Nat \X {1}
Init == x = 0
Next == x' = IF Same THEN 1 ELSE 2
Inv == x # 2
====
