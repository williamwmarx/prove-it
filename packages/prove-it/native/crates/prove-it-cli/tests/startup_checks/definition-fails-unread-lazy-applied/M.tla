---- MODULE M ----
EXTENDS Integers, TLC
Test == PrintT([x \in SUBSET {0} |-> {1} \cap 0][{}])
====
