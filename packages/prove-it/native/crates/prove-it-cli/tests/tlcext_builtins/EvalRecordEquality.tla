---- MODULE EvalRecordEquality ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME TLCEval([a |-> 1]) = 1
====
