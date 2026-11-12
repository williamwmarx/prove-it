---- MODULE GetOrDefaultNegative ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == TLCGetOrDefault(0 - 1, 0) = 0
====
