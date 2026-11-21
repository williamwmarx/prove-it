---- MODULE M ----
EXTENDS Integers, TLC
ASSUME /\ PrintT(TRUE) /\ PrintT({1,"a"} \cap Int)
====
