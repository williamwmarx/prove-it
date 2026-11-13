---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Test == Assert(FALSE, "boom")
Init == x = TRUE
Next == x' = Test
====
