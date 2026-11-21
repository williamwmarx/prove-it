---- MODULE M ----
EXTENDS Naturals,TLC
VARIABLE x
Init==x=0
Next==UNCHANGED x
K(a)==a
====
