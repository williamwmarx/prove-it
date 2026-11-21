---- MODULE M ----
EXTENDS Integers, TLC, TLCExt, FiniteSets

VARIABLE v
Init == v = ((65536*65536)=0)
Next == UNCHANGED v
====
