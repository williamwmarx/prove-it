---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = (LET S == [a : {1}] IN \E t \in {<<>>} : t \in S)
Next == x' = x
====
