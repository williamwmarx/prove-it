---- MODULE M ----
EXTENDS Integers, Sequences
VARIABLE x
D == Tail([<<>> EXCEPT ![1] = 0])
Init == x=0
Next == x'=1-x
Inv == x<1
====
