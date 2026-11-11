---- MODULE M ----
EXTENDS Ext, Naturals
VARIABLE v
Init == v = Pub
Next == UNCHANGED v
Inv == v = Op - 100
====
