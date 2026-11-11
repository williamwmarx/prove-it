---- MODULE M ----
EXTENDS Naturals, TLC
P(v) == v = v
ASSUME {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {} /\ P(1 \div 0)
====
