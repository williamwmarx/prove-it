---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
M == CASE ("a" \in UNION {1..2, {"a"}}) -> TRUE [] OTHER -> FALSE
Init == x = 0
Next == M /\ (x' = 1 - x \/ (x = 1 /\ x' = 1 + "a"))
====
