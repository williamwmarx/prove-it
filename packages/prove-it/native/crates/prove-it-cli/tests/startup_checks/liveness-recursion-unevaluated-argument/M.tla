---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
RECURSIVE F(_)
F(n) == <>(x = 0) /\ F(n)
Prop == F(1 \div 0)
====
