---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Test == Assert(FALSE, 42)
Init == x = Test
Next == x' = x
====
