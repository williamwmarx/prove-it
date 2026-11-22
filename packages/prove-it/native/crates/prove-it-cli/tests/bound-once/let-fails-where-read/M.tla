---- MODULE M ----
EXTENDS Integers, TLC
VARIABLES x
Pair(a) == <<a, a + 1>>
Init == x = 0
Next == x < 4 /\ x' = x + 1 /\ LET d == 10 \div (2 - x) IN (x < 2 \/ Pair(d)[1] > 0)
====
