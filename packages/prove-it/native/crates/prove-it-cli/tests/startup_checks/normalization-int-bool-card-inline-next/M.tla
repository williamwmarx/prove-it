---- MODULE M ----
EXTENDS Integers,FiniteSets,TLC,TLCExt,Sequences
VARIABLE x
Init == x = TRUE
Next == x' = (Cardinality(({1, TRUE}))=0)
Inv == x
====
