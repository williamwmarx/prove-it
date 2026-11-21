---- MODULE M ----
EXTENDS TLCExt, TLC, Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ ~AssertError("TLCGet(99) was undefined.", TLCGet(99)) /\ x' = x + 1
====
