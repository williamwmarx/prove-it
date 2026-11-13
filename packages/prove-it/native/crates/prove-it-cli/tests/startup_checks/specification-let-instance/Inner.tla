---- MODULE Inner ----
VARIABLES a, b, p
ISpec == a = 0 /\ b = 0 /\ [][a' = a /\ b' = b]_<<a, p>>
====
