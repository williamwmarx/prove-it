---- MODULE M ----
EXTENDS Integers
VARIABLE x
D == IF FALSE THEN [1 EXCEPT ![1]=0] ELSE 1
Init == x=0
Next == x'=x
====
