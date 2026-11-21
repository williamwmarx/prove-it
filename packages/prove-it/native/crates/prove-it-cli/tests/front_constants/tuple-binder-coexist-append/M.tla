---- MODULE M ----
EXTENDS Integers, TLC, Sequences
ASSUME PrintT(1 :> 2) /\ (\A <<a>> \in {Append(<<>>,2)}: a=2)
====
