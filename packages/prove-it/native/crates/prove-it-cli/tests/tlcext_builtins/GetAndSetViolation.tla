---- MODULE GetAndSetViolation ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x < 4 /\ x' = x + 1 /\ TLCGetAndSet(0, LAMBDA a, b : a + b, x, 100) # 0
Inv == PrintT(TLCGetOrDefault(0, x)) /\ x < 3
====
