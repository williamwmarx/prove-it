---- MODULE M ----
EXTENDS Naturals
VARIABLES x,y
Init==x=0 /\y=0
A==x'=5 /\UNCHANGED x /\y'=0
B==y<2 /\y'=y+1 /\UNCHANGED x
Next==A \/B
Inv==y=0
====
