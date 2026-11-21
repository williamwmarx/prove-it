---- MODULE LazyUnbuilt ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Unbuilt == PrintT([n \in UNION {{1}, 1..2} |-> 1 \div (n - 1)])
ASSUME Unbuilt
ASSUME PrintT([n \in UNION {{1}, 1..2} |-> 1 \div (n - 1)][2])
ASSUME [n \in 0 |-> 1] @@ (1 :> 2) = (1 :> 2)
====
