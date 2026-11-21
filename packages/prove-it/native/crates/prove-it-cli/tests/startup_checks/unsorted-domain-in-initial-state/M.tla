---- MODULE M ----
EXTENDS Integers, TLC
Test == [x \in {1} |-> [w \in {1, "a"} |-> 1]] = <<>>
VARIABLE v
Init == v = (Test)
Next == UNCHANGED v
====
