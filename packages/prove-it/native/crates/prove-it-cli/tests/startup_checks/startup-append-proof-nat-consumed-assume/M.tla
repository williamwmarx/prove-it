---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(Nat, IF {1,"a"} = {1,"a"} THEN 0 ELSE 1))
ASSUME Test
====
