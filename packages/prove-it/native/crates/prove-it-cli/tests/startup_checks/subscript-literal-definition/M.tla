---- MODULE M ----
EXTENDS Naturals
VARIABLES b, a
C == 1
Spec == b = 0 /\ a = 0 /\ [][UNCHANGED <<a, b>>]_<<a, b, C>>
====
