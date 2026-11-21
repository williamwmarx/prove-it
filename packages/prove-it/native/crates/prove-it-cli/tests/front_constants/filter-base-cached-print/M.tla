---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
B == Print("base",<<3,1,2,1>>)
ASSUME PrintT({y \in {x \in B : TRUE} : Print("unused",TRUE)})
====
