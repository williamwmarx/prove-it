---- MODULE M ----
EXTENDS Integers, Sequences, TLC
ASSUME (PrintT(Append(Nat, [x \in 1 \div 0 |-> x])))
====
