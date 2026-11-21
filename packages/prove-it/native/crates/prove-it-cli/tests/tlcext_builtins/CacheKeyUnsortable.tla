---- MODULE CacheKeyUnsortable ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME TLCCache(1 + 1, {1, "a"}) = 2
====
