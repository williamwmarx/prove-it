---- MODULE CacheRecordInvariant ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
Inv == TLCCache([a |-> 1], 1) = 1
====
