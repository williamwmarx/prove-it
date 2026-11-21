---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == UNCHANGED x
\* TLCEval of a constant argument builds each function constructor in it (`tlcEvalConst`), whose
\* domain fails to sort comparing the record with the tuple.
ASSUME TLCEval(<<[z \in {<<1>>, [a |-> 1]} |-> z]>>)[1][<<1>>] = <<1>>
====
