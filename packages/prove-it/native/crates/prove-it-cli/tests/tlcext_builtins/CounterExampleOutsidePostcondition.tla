---- MODULE CounterExampleOutsidePostcondition ----
EXTENDS Naturals, Sequences, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x /\ PrintT(CounterExample) /\ ToTrace(CounterExample) = <<>>
====
