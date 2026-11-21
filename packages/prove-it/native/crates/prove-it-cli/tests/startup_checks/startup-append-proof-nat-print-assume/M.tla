---- MODULE M ----
EXTENDS Integers, Sequences, TLC
ASSUME (PrintT(Append(Nat, IF PrintT("right") THEN Nat ELSE Int)))
====
