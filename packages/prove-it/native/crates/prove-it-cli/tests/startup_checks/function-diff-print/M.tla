---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
ASSUME PrintT([{1} -> {2, 3}] \ {1})
====
