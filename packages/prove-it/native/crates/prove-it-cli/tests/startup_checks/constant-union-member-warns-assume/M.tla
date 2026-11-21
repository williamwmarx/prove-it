---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
Test == "a" \in UNION {1..2, {"a"}} /\ [<<1>> EXCEPT ![2] = 3] = <<1>>
ASSUME Test
Init == x = 0
Next == UNCHANGED x
====
