---- MODULE M ----
EXTENDS Integers, TLC
ASSUME (CHOOSE <<a,b>> \in {[i \in 1..2 |-> i]}: TRUE) = <<1,2>>
====
