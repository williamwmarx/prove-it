---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
ASSUME PrintT({"a"} \cap (Int \X {}))
Init == x = 0
Next == x' = x
====
