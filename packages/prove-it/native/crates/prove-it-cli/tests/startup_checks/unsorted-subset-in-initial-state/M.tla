---- MODULE M ----
EXTENDS Integers, TLC
Test == 1 \in SUBSET {1, "a"}
VARIABLE v
Init == v = (Test)
Next == UNCHANGED v
====
