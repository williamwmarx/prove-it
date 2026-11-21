---- MODULE M ----
EXTENDS Integers, TLC
ASSUME \E <<a,b>> \in {(1 :> 5) @@ (2 :> 6)}: a = 5
====
