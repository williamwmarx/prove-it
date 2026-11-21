---- MODULE M ----
EXTENDS Naturals,TLC
VARIABLE x
K(n)==n
Init==x=0
Next==UNCHANGED x
====
