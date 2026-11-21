---- MODULE M ----
EXTENDS Integers,TLC,Sequences,TLCExt
VARIABLE x
Init == x=0
Next == x'=x+1
Inv == x < 1
Al == IF PrintT(<<"alias",x,Len(Trace)>>) THEN [x |-> x,t |-> Trace] ELSE [x |-> x]
Post == PrintT(CounterExample)
====
