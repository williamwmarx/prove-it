---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
ASSUME PrintT({y \in {x \in Print("base",<<3,1,2,1>>) : TRUE} : Print("unused",TRUE)})
====
