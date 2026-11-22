---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Init == x = 0
Next == SelectSeq(<<1>>, LAMBDA k : [a |-> x] = {x}) = <<>> /\ x' = x
====
