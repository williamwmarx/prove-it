---- MODULE M ----
EXTENDS Integers, TLC, TLCExt, FiniteSets

VARIABLE v
Spec == v=TRUE /\ [][UNCHANGED v]_v
Prop == [](v /\ ((-((0-2147483647-1)))=0))
====
