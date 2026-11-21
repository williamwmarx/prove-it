---- MODULE M ----
EXTENDS Integers,TLC,Sequences,TLCExt
VARIABLE x
Init == PrintT("init") /\ x=0
Next == x'=x+1
Inv == x < 1
Al == [x |-> x,t |-> Trace]
Post == PrintT(CounterExample)
====
