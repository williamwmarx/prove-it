---- MODULE M ----
EXTENDS Integers,TLC,Sequences,TLCExt
VARIABLE x
Init == x=0
Next == PrintT(<<"next",x>>) /\ x'=x+1
Inv == x < 1
Al == [x |-> x,t |-> Trace]
Post == PrintT(CounterExample)
====
