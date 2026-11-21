---- MODULE M ----
EXTENDS Integers,TLC,Sequences,TLCExt
VARIABLE x
Init == x=0
Next == (IF x=1 THEN PrintT("last") ELSE TRUE) /\ x'=x+1
Inv == x < 2
Al == [x |-> x,t |-> Trace]
Post == PrintT(CounterExample)
====
