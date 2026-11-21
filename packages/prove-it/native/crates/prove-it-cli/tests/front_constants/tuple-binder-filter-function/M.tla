---- MODULE M ----
EXTENDS Integers, TLC
ASSUME {<<a,b>> \in {[i \in 1..2 |-> i]}: TRUE} # {}
====
