---- MODULE CacheAfterPrint ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME PrintT(0) /\ TLCCache(1, 1 \div 0) = 1
====
