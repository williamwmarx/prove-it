---- MODULE EnumeratedTuple ----
EXTENDS Naturals
CONSTANTS M, T
VARIABLE x
Inv == <<<<x>>, 1>> \notin {<<<<1>>, 2>>, <<[a |-> 1], 3>>}
Init == x = 0
Next == x < 2 /\ x' = x + 1
Spec == Init /\ [][Next]_x
====
