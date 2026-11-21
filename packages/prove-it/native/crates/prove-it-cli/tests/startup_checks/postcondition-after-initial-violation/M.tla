---- MODULE M ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x \in 0..3
Next == UNCHANGED x
Inv == x < 2
Post == PrintT(CounterExample) /\ 1 \div 0 = 1
====
