---- MODULE M ----
EXTENDS Json, TLC, Integers
Test == PrintT("x") /\ ToJson(Nat) = ""
ASSUME Test
====
