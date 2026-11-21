---- MODULE M ----
VARIABLES x,y
V==L::x
Step(a)==UNCHANGED a
Init==x=0 /\y=0
Next==x'=1 /\ Step(V!L)
====
