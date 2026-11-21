---- MODULE M ----
EXTENDS Integers, TLC, TLCExt
VARIABLE x
Spec == x = 1 /\ [][UNCHANGED x]_x
Prop == [](DOMAIN [y \in 1..x, z \in 1..2 |-> 1 \div (x - x)] # {})
====
