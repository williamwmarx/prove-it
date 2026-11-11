---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x' = x
CONSTANT C
Foo == IF TLCGet("level") = 1 THEN x ELSE 2
====
