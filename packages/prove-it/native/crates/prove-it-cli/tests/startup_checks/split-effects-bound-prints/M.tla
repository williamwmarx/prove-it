---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE y
Init == y \in 0..3
Next == \E v \in (IF PrintT("domain") THEN 0..1 ELSE {}) : y' = v
====
