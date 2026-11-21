---- MODULE M ----
EXTENDS Naturals
VARIABLES x,y
Init==x=0 /\y=0
Next==x' \in 1..200 /\UNCHANGED x
====
