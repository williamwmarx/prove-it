---- MODULE M ----
EXTENDS Integers, TLC

VARIABLE x
Init == x = 0
Next == x' = (TRUE + <<1>>)
====
