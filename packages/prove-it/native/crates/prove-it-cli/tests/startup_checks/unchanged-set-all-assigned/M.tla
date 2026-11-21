---- MODULE M ----
EXTENDS Integers
VARIABLES x
Init == x = 0
Next == x' = "a" /\ UNCHANGED {x}
====
