---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x

Init == x = 0
Next == \E v \in (IF TLCGet("action") = TLCGet("action") THEN {0, 1} ELSE {0}) : x' = v
====
