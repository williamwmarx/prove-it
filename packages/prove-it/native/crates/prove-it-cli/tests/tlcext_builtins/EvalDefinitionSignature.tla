---- MODULE EvalDefinitionSignature ----
EXTENDS Naturals, Sequences, TLC, TLCExt
VARIABLE x
G(Op(_, _), a) == a
Init == x = 0
Next == x' = x /\ TLCEvalDefinition("G") = 0
====
