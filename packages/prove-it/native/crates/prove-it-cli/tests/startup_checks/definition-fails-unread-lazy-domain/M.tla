---- MODULE M ----
EXTENDS Integers, TLC
Test == PrintT(DOMAIN [x \in SUBSET {0} |-> {1} \cap 0])
====
