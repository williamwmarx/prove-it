---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
VARIABLE x
Init == x = 1 \/ x = 2
Next == UNCHANGED x
Inv == [y \in 1..x |-> 1 \div (x - x)] = <<>>
====
