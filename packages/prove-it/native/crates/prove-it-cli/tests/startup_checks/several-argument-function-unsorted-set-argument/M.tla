---- MODULE M ----
EXTENDS Integers, TLC
ASSUME [x \in {1}, y \in {2} |-> x][{1, "a"}] = 1
====
