---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Init == x = 0
Next == ({x} = <<x>>) = FALSE /\ x' = x
====
