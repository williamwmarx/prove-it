---- MODULE M ----
EXTENDS Naturals, FiniteSets, TLC
Test == PrintT({y \in {x \in 1 : FALSE} : TLCSet(0, 3)})
Count == Cardinality({y \in {x \in STRING : TLCSet(0, 3)} : 1}) = 0
ASSUME Test
ASSUME Count
====
