---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Init == x = 0
Next == SortSeq(<<1, 2>>, LAMBDA a, b : {x} = <<x>>) = <<>> /\ x' = x
====
