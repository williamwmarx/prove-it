---- MODULE SearchedRecord ----
EXTENDS Naturals
CONSTANTS M, T
VARIABLE x
S == {[i \in 0..1 |-> 5]}
Inv == [a |-> x] \notin S
Init == x = 0
Next == x < 2 /\ x' = x + 1
Spec == Init /\ [][Next]_x
====
