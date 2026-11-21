---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Next == x<2 /\ x'=x+1
Spec == x=0 /\ [][Next]_x /\ WF_x(Next)
Prop == <>(LET RECURSIVE R, S R == S S == R IN R)
====
