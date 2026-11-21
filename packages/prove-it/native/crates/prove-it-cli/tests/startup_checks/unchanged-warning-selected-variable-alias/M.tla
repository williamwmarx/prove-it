---- MODULE M ----
VARIABLES x,y
V==L::x
S==V!L
Init==x=0 /\y=0
Next==x'=1 /\ UNCHANGED (S)
====
