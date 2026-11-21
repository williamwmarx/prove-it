---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
VARIABLE x
D == TLCGetOrDefault(-1, "d")
Init == x = D
Next == UNCHANGED x
====
