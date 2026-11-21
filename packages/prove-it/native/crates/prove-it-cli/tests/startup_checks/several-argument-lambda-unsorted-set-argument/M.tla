---- MODULE M ----
EXTENDS Integers, TLC
ASSUME [x \in Nat, y \in Nat |-> x][{1, TRUE}] = 1
====
