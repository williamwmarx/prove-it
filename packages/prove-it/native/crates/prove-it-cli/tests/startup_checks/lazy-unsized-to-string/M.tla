---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = ToString([a : Int, b : {}])
Next == x' = x
====
