---- MODULE M ----
EXTENDS Integers, TLC, FiniteSets
VARIABLE v
D0 == Cardinality({PrintT(x) : x \in <<>>})
D2 == [x \in {1, 2} |-> <<"a", D0>>] \cup {x \in 1..3 : TRUE}
Init == v = 0
Next == v' = v
====
