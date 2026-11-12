---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = 0
Next == x' = x
CONSTANT C
Foo == (1 \div 0) + x
====
