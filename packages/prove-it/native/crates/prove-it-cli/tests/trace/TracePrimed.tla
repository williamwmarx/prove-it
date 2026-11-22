---- MODULE TracePrimed ----
EXTENDS TLCExt, Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x' = (Trace')[1].x
====
