---- MODULE M ----
EXTENDS Integers,TLC,Sequences,TLCExt
VARIABLE x
Init == x=0
Next == PrintT(<<"next",x>>) /\ x'=x+1
Inv == x < 2
Al == [x |-> x,t |-> IF x=0 THEN Trace ELSE <<>>]
Post == PrintT(CounterExample)
====
