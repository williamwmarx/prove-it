---- MODULE EvalDefinitionInvariant ----
EXTENDS Naturals, Sequences, TLC, TLCExt
VARIABLE x
D == x + 1
Init == x = 0
Next == x' = (x + 1) % 3
Inv == TLCEvalDefinition("D") = x + 1
====
