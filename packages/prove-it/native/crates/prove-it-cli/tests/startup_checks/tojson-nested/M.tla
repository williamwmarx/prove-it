---- MODULE M ----
EXTENDS Integers, TLC, Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJson(<<{1,2}, [a |-> <<3,4>>]>>))
Next == x' = x
====
