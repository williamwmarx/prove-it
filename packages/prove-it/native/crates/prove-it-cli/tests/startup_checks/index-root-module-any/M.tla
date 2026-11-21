---- MODULE M ----
EXTENDS TLC
Test == 1 \in Any
VARIABLE s
Init == s = Test
Next == UNCHANGED s
Inv == s
====
