---- MODULE M ----
EXTENDS Integers
VARIABLE x
CONSTANT C
Foo == 1 \div 0
Init == x = C
Next == x' = x
====
