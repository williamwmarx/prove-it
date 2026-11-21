---- MODULE M ----
EXTENDS Naturals
VARIABLE x
---- MODULE Abs ----
VARIABLE v
AInit == v=0
Alias == AInit
ANext == UNCHANGED v
ASpec == Alias /\ [][ANext]_v
====
N == UNCHANGED x
Spec == x=0 /\ [][N]_x
A(y) == INSTANCE Abs WITH v <- y
Prop == A(x+1)!ASpec
====
