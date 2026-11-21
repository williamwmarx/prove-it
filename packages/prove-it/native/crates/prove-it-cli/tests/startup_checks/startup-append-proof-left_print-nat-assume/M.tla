---- MODULE M ----
EXTENDS Integers, Sequences, TLC
ASSUME (PrintT(Append(IF PrintT("left") THEN BOOLEAN ELSE {}, Nat)))
====
