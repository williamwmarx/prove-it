---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
ASSUME PrintT({y \in {x \in 1 : 1 \div 0 = 0} : Print("unused",TRUE)})
====
