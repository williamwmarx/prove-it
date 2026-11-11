---- MODULE M ----
EXTENDS Naturals, TLC
P(v) == v = v
ASSUME {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {} /\ P(RandomElement(1..1000))
====
