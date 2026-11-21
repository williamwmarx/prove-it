---- MODULE M ----
EXTENDS Integers, TLC
ASSUME \E <<a,b>> \in {[i \in 1..2 |-> i]}: a = 1
====
