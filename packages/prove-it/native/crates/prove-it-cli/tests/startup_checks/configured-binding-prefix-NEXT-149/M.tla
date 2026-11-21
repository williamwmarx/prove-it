---- MODULE M ----
EXTENDS TLC,Naturals
VARIABLE x
D==1\div0
K==x=0
Init==x=0
Next==UNCHANGED x
====
