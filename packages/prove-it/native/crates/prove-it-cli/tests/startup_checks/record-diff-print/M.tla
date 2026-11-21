---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
ASSUME PrintT([a : {1, 2}] \ {1})
====
