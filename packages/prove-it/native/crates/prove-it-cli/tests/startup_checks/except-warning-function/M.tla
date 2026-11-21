---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
ASSUME PrintT([((1 :> 2) @@ (2 :> 3)) EXCEPT ![3] = 1 \div 0, ![1] = @+1])
Init == x=0
Next == x'=x
====
