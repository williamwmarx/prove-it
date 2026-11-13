---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = ToString([a : STRING, b : {}] \ {1})
Inv == x = "{}"
Next == x' = x
====
