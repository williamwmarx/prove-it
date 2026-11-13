---- MODULE Inner2 ----
VARIABLES a, b
K == 1
Kp(z) == 1
ISpec == a = 0 /\ b = 0 /\ [][a' = a /\ b' = b]_<<a, K, Kp(0)>>
====
