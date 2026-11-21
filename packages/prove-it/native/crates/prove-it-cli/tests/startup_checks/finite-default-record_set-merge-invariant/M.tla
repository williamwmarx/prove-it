---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Init == x = TRUE
Next == UNCHANGED x
Inv == PrintT(([a: {1,2}, b: {3}]) @@ (1 :> 1))
====
