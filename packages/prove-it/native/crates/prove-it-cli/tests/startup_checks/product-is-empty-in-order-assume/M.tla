---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == PrintT((((<<1>> \X {}) \X UNION {2, 1, 3}) \ {b \in DOMAIN [x \in {} |-> 1] : ~TRUE}))
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
