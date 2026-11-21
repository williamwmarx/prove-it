---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE s
Init == s = FALSE
Next == s' = (\E p \in {q \in (1..1001) \X (1..1000) : TRUE} : TRUE)
====
