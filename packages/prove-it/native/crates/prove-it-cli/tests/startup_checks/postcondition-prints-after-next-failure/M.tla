---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 \div x
Post == PrintT(<<7, TLCGet("level")>>) /\ FALSE
====
