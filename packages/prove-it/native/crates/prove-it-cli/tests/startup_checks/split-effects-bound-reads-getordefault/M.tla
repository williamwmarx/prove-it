---- MODULE M ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x

Init == x = 0
Next == \E v \in (TLCGetOrDefault("not-a-register", {0, 1})) : x' = v
====
