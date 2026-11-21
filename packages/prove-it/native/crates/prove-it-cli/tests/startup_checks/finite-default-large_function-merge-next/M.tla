---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Init == x = TRUE
Next == x' = PrintT(([1..11 -> BOOLEAN]) @@ (1 :> 1))
====
