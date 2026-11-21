---- MODULE CacheKeyNat ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME TLCCache(1 + 1, Nat) = 2
====
