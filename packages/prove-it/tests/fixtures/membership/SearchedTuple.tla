---- MODULE SearchedTuple ----
EXTENDS Naturals
CONSTANTS M, T
VARIABLE x
S == {<<[a |-> 1]>>, <<[a |-> 2]>>}
Inv == <<<<x>>>> \notin S
Init == x = 0
Next == x < 2 /\ x' = x + 1
Spec == Init /\ [][Next]_x
====
