---- MODULE ActionAndAllRegisters ----
EXTENDS Naturals, Sequences, TLC, TLCExt
VARIABLE x
Init == x = 0 /\ TLCSet(2, "r")
Next == x' = (x + 1) % 2 /\ PrintT(<<TLCGet("action").name, TLCGet("all")>>)
====
