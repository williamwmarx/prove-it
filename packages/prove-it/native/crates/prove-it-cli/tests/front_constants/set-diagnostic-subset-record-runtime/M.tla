---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = PrintT([b |-> 2, a |-> 1] \subseteq TLCGet("level"))
Next == UNCHANGED x
====
