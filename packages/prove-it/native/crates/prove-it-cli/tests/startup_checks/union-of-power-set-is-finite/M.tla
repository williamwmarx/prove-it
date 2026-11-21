---- MODULE M ----
EXTENDS Integers, FiniteSets
VARIABLE x
S == SUBSET {1, 2}
Init == x = IsFiniteSet(UNION S)
Next == x' = IsFiniteSet(UNION SUBSET SUBSET {1})
Inv == x
====
