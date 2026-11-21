---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE x
Init == x=0
Next == x'=x
P(v) == \A y \in Seq({1}) : x=v
Prop == <>P(0)
====
