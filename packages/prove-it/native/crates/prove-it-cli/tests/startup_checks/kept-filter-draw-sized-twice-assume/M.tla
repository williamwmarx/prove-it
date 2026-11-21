---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC, Randomization
D == {i \in 1..20 : RandomElement({TRUE, FALSE})}
ASSUME Cardinality(D) = Cardinality(D)
====
