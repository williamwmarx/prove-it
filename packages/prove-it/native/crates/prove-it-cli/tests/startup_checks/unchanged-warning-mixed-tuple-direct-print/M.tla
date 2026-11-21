---- MODULE M ----
EXTENDS TLC
VARIABLES x,y

Init==x=0 /\ y=0
Next==x'=1 /\ UNCHANGED (<<x,PrintT(17)>>)
====
