---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
Init == x = 0 /\ PrintT(ToJsonArray(3 :> "c" @@ 1 :> "a"))
Next == x' = x
====
