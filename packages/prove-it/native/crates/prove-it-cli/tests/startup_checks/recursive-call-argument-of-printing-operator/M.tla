---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
P(m, v) == IF PrintT(m) THEN v ELSE v
RECURSIVE R(_)
R(n) == IF n = 0 THEN 0 ELSE P(n, R(n - 1))
Test == R(3) = 0
ASSUME Test
Init == x = R(2)
Next == x < 1 /\ x' = x + 1
====
