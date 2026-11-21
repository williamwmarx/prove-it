---- MODULE M ----
EXTENDS Integers, TLC
ASSUME PrintT((2 :> {2, "x"}) @@ (1 :> {1, "y"}))
====
