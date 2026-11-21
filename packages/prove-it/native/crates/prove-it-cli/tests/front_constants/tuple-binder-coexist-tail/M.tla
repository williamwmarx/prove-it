---- MODULE M ----
EXTENDS Integers, TLC, Sequences
ASSUME PrintT(1 :> 2) /\ (\A <<a>> \in {Tail(<<0,2>>)}: a=2)
====
