---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = PrintT(<<[a : {}, b : Int]>>)
Next == x' = x
====
