---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Step == <<TRUE>>[1] /\ <<1>>[1]
====
