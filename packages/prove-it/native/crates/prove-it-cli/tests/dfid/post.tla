---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2
Post == PrintT(<<"post", TLCGet("level")>>)
====
