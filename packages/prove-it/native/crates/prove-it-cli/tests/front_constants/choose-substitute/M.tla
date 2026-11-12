---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = 0
Next == x' = x
CONSTANT C
Foo == IF CHOOSE n \in {} : TRUE THEN x ELSE x
====
