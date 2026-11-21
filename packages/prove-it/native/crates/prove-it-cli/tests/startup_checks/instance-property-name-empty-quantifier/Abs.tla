---- MODULE Abs ----
CONSTANT S
VARIABLE v
AInit == \A k \in S : v=0
ANext == UNCHANGED v
ASpec == AInit /\ [][ANext]_v
====
