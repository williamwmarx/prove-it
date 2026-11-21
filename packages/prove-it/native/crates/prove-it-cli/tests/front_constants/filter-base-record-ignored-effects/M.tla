---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
ASSUME PrintT({y \in {x \in [a |-> 1] : TLCGet(0) = 0} : Print("unused",TRUE)})
====
