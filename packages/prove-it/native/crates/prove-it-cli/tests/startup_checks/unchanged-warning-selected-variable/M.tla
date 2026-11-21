---- MODULE M ----
VARIABLES x,y
V==L::x
Init==x=0 /\ y=0
Next==x'=1 /\ UNCHANGED (V!L)
====
