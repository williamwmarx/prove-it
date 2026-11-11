---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x' = x
CONSTANT C
Foo == TLCGet(3)
====
