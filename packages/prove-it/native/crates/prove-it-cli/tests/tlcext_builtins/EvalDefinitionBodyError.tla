---- MODULE EvalDefinitionBodyError ----
EXTENDS Naturals, Sequences, TLC, TLCExt
VARIABLE x
D == {1} \cup 2
Init == x = 0
Next == x' = x
Inv == TLCEvalDefinition("D") = {}
====
