---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
ASSUME PrintT(IsFiniteSet([a : {}, b : Int] \ Seq({1 \div 0}))) \/ TRUE
Init == x = 0
Next == UNCHANGED x
====
