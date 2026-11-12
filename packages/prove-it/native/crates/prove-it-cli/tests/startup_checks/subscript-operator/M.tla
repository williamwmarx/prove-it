---- MODULE M ----
EXTENDS Naturals
VARIABLES b, a
V(v) == v
Spec == b = 0 /\ a = 0 /\ [][UNCHANGED <<a, b>>]_<<V(a), b>>
====
