---- MODULE M ----
EXTENDS Naturals
VARIABLES x, h
Next == x' = (x + 1) % 2 /\ h' = h
Spec == x = 0 /\ h = 0 /\ [][Next]_<<x, h>> /\ WF_<<x, h>>(Next)
Vw == x'
Prop == <>(x = 0)
====
