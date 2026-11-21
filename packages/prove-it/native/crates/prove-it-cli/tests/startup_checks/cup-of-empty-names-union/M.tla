---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = TRUE
Next == x' = (({} \cup {1, "a"}) = {})
====
