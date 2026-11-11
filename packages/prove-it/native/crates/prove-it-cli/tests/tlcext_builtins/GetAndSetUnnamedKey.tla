---- MODULE GetAndSetUnnamedKey ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1 /\ TLCGetAndSet("foo", LAMBDA a, b : b, 1, 0) = 0
====
