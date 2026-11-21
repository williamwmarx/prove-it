---- MODULE M ----
EXTENDS Integers,FiniteSets,TLC,TLCExt,Sequences
VARIABLE x
Init == x = (Cardinality(({1, TRUE}))=0)
Next == UNCHANGED x
Inv == x
====
