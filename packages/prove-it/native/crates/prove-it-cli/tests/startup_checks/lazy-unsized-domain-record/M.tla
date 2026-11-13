---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = DOMAIN [k |-> [Int -> {}]]
Inv == x = {"k"}
Next == x' = x
====
