---- MODULE M ----
EXTENDS Integers,TLC,Sequences,TLCExt
VARIABLE x
Init == x=0
Next == x'=x+1
Inv == x < 1
Al == LET v == [[a |-> x] EXCEPT !.b=0] IN [x |-> x,t |-> Trace,v |-> v]
Post == PrintT(CounterExample)
====
