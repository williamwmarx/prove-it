---- MODULE M ----
EXTENDS TLC
VARIABLE s
Test == 1 \in Any
Init == s = Test
Next == UNCHANGED s
Inv == s
====
