---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = Cardinality({} \ [Int -> {CHOOSE c \in {} : TRUE}])
Next == UNCHANGED x
====
