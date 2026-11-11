---- MODULE M ----
EXTENDS Integers
VARIABLE x
CONSTANT C
Foo == (1 % 0) + x
Init == x = 0
Next == x' = x
====
