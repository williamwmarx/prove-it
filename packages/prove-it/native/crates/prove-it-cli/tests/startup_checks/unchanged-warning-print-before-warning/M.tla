---- MODULE M ----
EXTENDS TLC
VARIABLES x,y
Id(a)==a
Step(a)==UNCHANGED a
BothStep(a)==UNCHANGED <<a,y>>
Init==x=0 /\ y=0
Next==PrintT(77) /\ x'=1 /\ UNCHANGED x
====
