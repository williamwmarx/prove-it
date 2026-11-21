---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE x
Init == x=0
Next == x'=x
P == \A y \in Seq({1}) : x=0
Prop == <>P
====
