---- MODULE M ----
EXTENDS Integers, TLC, Sequences
ASSUME PrintT([v \in {1} |-> 2]) /\ (\A <<a>> \in {<<2>>}: a=2)
====
