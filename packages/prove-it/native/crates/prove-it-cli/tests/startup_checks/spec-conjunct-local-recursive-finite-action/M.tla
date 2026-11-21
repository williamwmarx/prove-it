---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Next == x<2 /\ x'=x+1
Spec == x=0 /\ (LET RECURSIVE R(_) R(a) == IF a=0 THEN Next ELSE R(a-1) IN R(0))
====
