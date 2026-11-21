---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
Member == 1 \in UNION {{"a"}, 1..2}
Init == x = Member
Next == x' = ~x
====
