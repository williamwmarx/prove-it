---- MODULE M ----
EXTENDS Integers, TLC
Test == PrintT([f : {}, g : {1, "a"}]) /\ PrintT([{} -> {1, "a"}])
ASSUME Test
====
