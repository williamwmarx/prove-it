---- MODULE M ----
VARIABLES x,y
V(a)==L::a
Init==x=0 /\ y=0
Next==x'=1 /\ UNCHANGED (V(x)!L)
====
