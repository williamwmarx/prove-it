---- MODULE M ----
EXTENDS Integers,TLC,TLCExt
F == [k \in {1,2} |-> k]
ASSUME (DOMAIN F)+1
====
