---- MODULE TracePrimedSubstituted ----
EXTENDS TLCExt, Naturals, Sequences
CONSTANT F(_)
VARIABLE x
Init == x = 0
Next == x' = (F(0)')[1].x
====
