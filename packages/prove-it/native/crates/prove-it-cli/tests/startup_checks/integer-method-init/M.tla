---- MODULE M ----
EXTENDS Integers, TLC

VARIABLE x
Init == x = (TRUE + <<1>>)
Next == UNCHANGED x
====
