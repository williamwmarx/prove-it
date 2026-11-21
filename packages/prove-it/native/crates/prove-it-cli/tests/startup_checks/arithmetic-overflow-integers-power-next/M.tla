---- MODULE M ----
EXTENDS Integers, TLC, TLCExt, FiniteSets

VARIABLE v
Init == v = TRUE
Next == v' = ((2^31)=0)
====
