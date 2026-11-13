---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Test == Print(1 \div 0, TRUE)
Init == x = Test
Next == x' = x
====
