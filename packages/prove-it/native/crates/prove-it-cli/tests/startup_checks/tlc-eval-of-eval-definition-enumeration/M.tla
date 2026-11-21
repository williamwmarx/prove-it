---- MODULE M ----
EXTENDS TLCExt, TLC, Naturals
VARIABLE x
D == {1} \cup 2
Init == x = 0 /\ TLCEval(TLCEvalDefinition("D")) = {}
Next == UNCHANGED x
====
