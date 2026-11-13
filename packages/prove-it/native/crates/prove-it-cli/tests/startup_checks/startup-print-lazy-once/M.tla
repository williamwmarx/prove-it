---- MODULE M ----
EXTENDS Naturals, TLC
Test == PrintT([i \in {2, 1} |-> i])
ASSUME Test
ASSUME Test /\ Test
====
