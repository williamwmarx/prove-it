---- MODULE M ----
EXTENDS TLC
VARIABLES x,y
Id(a)==a
Step(a)==UNCHANGED a
BothStep(a)==UNCHANGED <<a,y>>
Init==x=0 /\ y=0
Next==FALSE /\ x'=1 /\ UNCHANGED x
====
