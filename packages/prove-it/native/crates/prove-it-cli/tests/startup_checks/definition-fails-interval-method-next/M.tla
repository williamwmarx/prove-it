---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Test == Assert(DOMAIN <<1>> = TRUE, "m")
Init == x = TRUE
Next == x' = Test
====
