---- MODULE GetOrDefault ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == /\ PrintT(<<TLCGetOrDefault("level", 7), TLCGetOrDefault({1}, 8), TLCGetOrDefault(3, x)>>)
       /\ TLCSet(3, x + 10)
====
