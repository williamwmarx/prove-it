---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
ASSUME PrintT([<<1>> EXCEPT ![0] = 1 \div 0, ![1] = @+1, ![2] = Print(99,0)])
Init == x=0
Next == x'=x
====
