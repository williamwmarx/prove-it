---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Test == 1 \in ({2} \cup [{1} -> {1, "a"}])
Init == x = TRUE
Next == x' = Test
====
