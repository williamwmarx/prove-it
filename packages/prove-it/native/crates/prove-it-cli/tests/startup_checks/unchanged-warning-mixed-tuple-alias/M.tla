---- MODULE M ----
EXTENDS TLC
VARIABLES x,y
Both==<<x,1>>
Init==x=0 /\ y=0
Next==x'=1 /\ UNCHANGED (Both)
====
