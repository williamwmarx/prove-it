---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = TRUE
Next == x' = (1 \in [{1} -> {1, <<1>>}])
====
