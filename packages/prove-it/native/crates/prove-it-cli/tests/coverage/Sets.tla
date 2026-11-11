---- MODULE Sets ----
EXTENDS Naturals, FiniteSets
VARIABLES s, f
Init == s = {} /\ f = [i \in {1, 2} |-> 0]
Grow == /\ s' \in SUBSET (s \cup {Cardinality(s) + 1})
        /\ f' \in [{1, 2} -> {0, 1}]
Next == Grow
Typed == /\ s \in SUBSET (1..5)
         /\ f \in [{1, 2} -> 0..1]
         /\ {e \in s : e > 1} \subseteq s
Small == Cardinality(s) < 4
====
