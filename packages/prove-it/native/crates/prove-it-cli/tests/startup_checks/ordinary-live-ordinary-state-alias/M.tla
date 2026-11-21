---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE x
Init == x=0
Next == x'=x
A == TRUE
B == x=0
P == A /\ (\A y \in Seq({1}):TRUE)
Prop == <>P
====
