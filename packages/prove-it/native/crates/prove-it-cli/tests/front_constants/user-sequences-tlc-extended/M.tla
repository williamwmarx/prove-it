---- MODULE M ----
EXTENDS TLC, Naturals, Sequences
ASSUME PrintT(Len(<<1>>))
VARIABLE x
Init == x = 0
Next == x' = x
====
