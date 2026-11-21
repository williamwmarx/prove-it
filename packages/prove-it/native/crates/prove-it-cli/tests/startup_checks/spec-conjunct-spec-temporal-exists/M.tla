---- MODULE M ----
VARIABLE x
Spec == \EE y : x=0 /\ y=0 /\ [][x'=x /\ y'=y]_<<x,y>>
====
