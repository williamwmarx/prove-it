---- MODULE Aid ----
EXTENDS Naturals
VARIABLE y
A == y<2 /\ y'=y+1
L == WF_y(A)
Spec == y=0 /\ [][A]_y /\ L
====
