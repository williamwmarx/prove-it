---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
VARIABLE x
Init == x \in {1, 2}
Next == UNCHANGED x
Inv == [y \in 1..x |-> CHOOSE z \in {} : TRUE] = <<>>
====
