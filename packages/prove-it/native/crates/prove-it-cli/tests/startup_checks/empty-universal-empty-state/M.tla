---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x'=x
Spec == Init /\ [][Next]_x
Id(p) == p
Other == <>(x=0)
Prop == \A n \in {} : x=0
====
