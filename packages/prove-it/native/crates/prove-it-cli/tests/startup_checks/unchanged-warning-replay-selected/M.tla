---- MODULE M ----
VARIABLES x,y
V==L::x
Init==x=0 /\y=0
A==x'=5 /\UNCHANGED (V!L) /\y'=0
B==y'=1 /\UNCHANGED x
Next==A \/B
Inv==y=0
====
