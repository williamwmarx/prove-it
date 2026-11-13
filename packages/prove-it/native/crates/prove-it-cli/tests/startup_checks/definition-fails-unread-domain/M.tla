---- MODULE M ----
EXTENDS Integers, TLC
Test == PrintT(DOMAIN [x \in {0, 1} |-> {1} \cap 0])
====
