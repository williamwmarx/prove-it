---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Inv == x < 2
====
