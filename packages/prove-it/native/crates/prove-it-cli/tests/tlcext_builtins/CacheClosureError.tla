---- MODULE CacheClosureError ----
EXTENDS Naturals, Sequences, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
Inv == TLCCache(TRUE, <<1>>[2])
====
