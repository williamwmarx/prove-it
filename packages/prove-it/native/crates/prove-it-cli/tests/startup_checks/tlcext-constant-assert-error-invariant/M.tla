---- MODULE M ----
EXTENDS Integers, Sequences, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == AssertError("wrong", Head(<<>>))
====
