---- MODULE PassedShallow ----
EXTENDS Naturals
VARIABLE x
RECURSIVE D(_)
D(n) == IF n = 0 THEN TRUE ELSE D(n - 1)
RECURSIVE F(_)
F(n) == IF n = 0 THEN TRUE ELSE (({[a |-> 1]} \cup ({n} \ {n})) \in SUBSET {e \in [a : {1, 2}] : D(100)}) /\ F(n - 1)
Init == x = 0
Next == x' = x
Inv == F(100)
====
