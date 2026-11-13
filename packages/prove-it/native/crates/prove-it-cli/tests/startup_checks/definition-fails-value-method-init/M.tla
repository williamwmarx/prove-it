---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Test == PrintT(DOMAIN <<1>> = TRUE)
Init == x = Test
Next == x' = x
====
