---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == \E v \in (IF TLCGet("config").deadlock THEN {0, 1} ELSE {0, 1}) : x' = v
====
