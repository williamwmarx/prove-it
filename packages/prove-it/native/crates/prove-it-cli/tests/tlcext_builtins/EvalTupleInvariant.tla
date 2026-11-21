---- MODULE EvalTupleInvariant ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
Inv == TLCEval(<<>>) = 1
====
