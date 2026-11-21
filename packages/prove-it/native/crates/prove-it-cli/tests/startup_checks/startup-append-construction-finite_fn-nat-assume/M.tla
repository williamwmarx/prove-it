---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append([x \in {"a"} |-> 1], Nat))
ASSUME Test
====
