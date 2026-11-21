---- MODULE CacheLiteral ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
Inv == TLCCache(2, 7) = 2
====
