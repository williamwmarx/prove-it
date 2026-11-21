---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = TRUE
Next == x' = PrintT(<<1,2>> \subseteq TLCGet("level"))
====
