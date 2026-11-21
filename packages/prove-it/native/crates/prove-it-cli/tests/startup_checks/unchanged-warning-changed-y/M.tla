---- MODULE M ----
EXTENDS TLC
VARIABLES x,y
Id(a)==a
Step(a)==UNCHANGED a
BothStep(a)==UNCHANGED <<a,y>>
Init==x=0 /\ y=0
Next==y'=2 /\ UNCHANGED <<x,y>>
====
