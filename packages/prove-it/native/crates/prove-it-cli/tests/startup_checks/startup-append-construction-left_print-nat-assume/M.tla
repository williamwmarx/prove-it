---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(IF PrintT("left") THEN BOOLEAN ELSE {}, Nat))
ASSUME Test
====
