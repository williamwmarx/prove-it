---- MODULE M ----
EXTENDS Integers, TLC, Json
VARIABLE x
RECURSIVE F(_)
F(n) == IF n = 0 THEN 0 ELSE <<F(n - 1)>>
Init == x = 0 /\ PrintT(ToJson(F(256)))
Next == x' = x
====
