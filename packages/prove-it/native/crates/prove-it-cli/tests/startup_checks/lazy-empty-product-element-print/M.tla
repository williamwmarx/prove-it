---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
ASSUME PrintT({Int \X {}})
Init == x = 0
Next == x' = x
====
