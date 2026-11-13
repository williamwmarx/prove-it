---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x = {[a : STRING, b : {}]}
Inv == x = {}
Next == x' = x
====
