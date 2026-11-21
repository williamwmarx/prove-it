---- MODULE M ----
EXTENDS Integers,TLC,TLCExt
F == [k \in {j : j \in SUBSET {1}} |-> k]
ASSUME (DOMAIN F)+1
====
