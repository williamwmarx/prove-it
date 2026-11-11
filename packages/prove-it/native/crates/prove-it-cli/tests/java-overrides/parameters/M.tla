---- MODULE M ----
EXTENDS Ext, Naturals
VARIABLE v
Init == v = Pub(1)
Next == UNCHANGED v
Inv == v = 2
====
