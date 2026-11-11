---- MODULE M ----
EXTENDS Naturals, TLC
ASSUME {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {} /\ (LET v == Print("let", TRUE) IN v /\ v)
====
