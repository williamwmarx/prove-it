---- MODULE M ----
EXTENDS Naturals
VARIABLE x
---- MODULE Abs ----
VARIABLE v
AInit(q) == v=q
ANext == UNCHANGED v
ASpec == AInit(0) /\ [][ANext]_v
====
N == UNCHANGED x
Spec == x=0 /\ [][N]_x
A(y) == INSTANCE Abs WITH v <- y
Prop == A(x+1)!ASpec
====
