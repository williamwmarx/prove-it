---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x'=x
Spec == Init /\ [][Next]_x
Id(p) == p
Other == <>(x=0)
Body(n) == IF PrintT("body") THEN <>(x=n) ELSE <>(x=n)
Prop == \A n \in {} : Body(n)
====
