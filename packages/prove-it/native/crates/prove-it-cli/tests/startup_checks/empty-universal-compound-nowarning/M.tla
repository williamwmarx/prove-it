---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x'=x
Spec == Init /\ [][Next]_<<>>
Id(p) == p
Other == <>(x=0)
Constant == TRUE
State == x=0
Prop == \A n \in {} : x=0
====
