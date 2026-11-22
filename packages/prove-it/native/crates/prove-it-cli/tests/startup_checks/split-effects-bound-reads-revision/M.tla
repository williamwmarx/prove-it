---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x

Init == x = 0
Next == \E v \in (IF "count" \in DOMAIN TLCGet("revision") THEN {0, 1} ELSE {0}) : x' = v
====
