---- MODULE M ----
EXTENDS TLC, Integers, Sequences
VARIABLE x
A == Any
ASSUME Seq(A) = Seq({1})
Init == x = 0
Next == x' = x
====
