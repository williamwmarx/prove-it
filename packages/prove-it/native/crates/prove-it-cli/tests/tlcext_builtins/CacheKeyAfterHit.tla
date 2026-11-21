---- MODULE CacheKeyAfterHit ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME \A k \in {1, 2} : TLCCache(k + 0, IF k = 1 THEN 1 ELSE {1, "a"}) = k
====
