---- MODULE M ----
EXTENDS Integers,TLC,Sequences,TLCExt
VARIABLE x
Init == x=0
Next == x'=x+1
Inv == x < 1
Al == IF Len(Trace)=0 THEN [x |-> x] ELSE IF PrintT(<<"worker",Len(Trace)>>) THEN [x |-> x] ELSE [x |-> x]
Post == PrintT(CounterExample)
====
