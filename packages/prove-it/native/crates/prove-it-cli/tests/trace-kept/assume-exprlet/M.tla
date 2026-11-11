---- MODULE M ----
EXTENDS Naturals, TLC
ASSUME {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {} /\ (LET F == [i \in Nat |-> i] IN F[0] + F[1]) = 1
====
