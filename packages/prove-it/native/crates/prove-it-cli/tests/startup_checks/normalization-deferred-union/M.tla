---- MODULE M ----
EXTENDS Integers,FiniteSets,TLC,TLCExt
VARIABLE x
Init == x=(Cardinality((UNION {{1},{"a"}}))=0)
Next == UNCHANGED x
Inv == x
====
