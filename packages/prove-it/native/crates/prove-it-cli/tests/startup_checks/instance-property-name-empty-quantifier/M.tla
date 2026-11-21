---- MODULE M ----
EXTENDS Naturals
VARIABLE x
N == UNCHANGED x
Spec == x=0 /\ [][N]_x
A(y) == INSTANCE Abs WITH v <- y, S <- {}
Prop == A(x+1)!ASpec
====
