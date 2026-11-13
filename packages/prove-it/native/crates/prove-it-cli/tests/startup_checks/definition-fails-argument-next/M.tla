---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Test == Assert(1 \div 0 = 0, "m")
Init == x = TRUE
Next == x' = Test
====
