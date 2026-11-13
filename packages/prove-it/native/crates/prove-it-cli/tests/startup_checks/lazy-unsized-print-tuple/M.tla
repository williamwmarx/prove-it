---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = PrintT(<<[a : Int, b : {}]>>)
Next == x' = x
====
