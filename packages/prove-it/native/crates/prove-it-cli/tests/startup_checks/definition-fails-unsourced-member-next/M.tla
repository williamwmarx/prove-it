---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Test == Print("x", <<1>> \in 0)
Init == x = TRUE
Next == x' = Test
====
