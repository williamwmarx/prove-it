---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
VARIABLE x
Bad == PrintT("p") /\ CHOOSE y \in {} : TRUE
Init == x = 0 /\ Bad
Next == UNCHANGED x
====
