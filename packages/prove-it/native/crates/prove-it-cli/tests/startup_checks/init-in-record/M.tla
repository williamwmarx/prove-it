---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
VARIABLE x
Init == x \in [a |-> 1]
Next == UNCHANGED x
====
