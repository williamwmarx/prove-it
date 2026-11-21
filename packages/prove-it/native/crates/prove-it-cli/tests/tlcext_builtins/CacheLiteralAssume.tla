---- MODULE CacheLiteralAssume ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME TLCCache("s", 1) = "s"
====
