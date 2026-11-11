---- MODULE GetAndSetCount ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1 /\ TLCGetAndSet(1, LAMBDA old, new : old + new, 10, 0) # 5
Inv == PrintT(<<x, TLCGetOrDefault(1, "unset")>>)
====
