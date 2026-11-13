---- MODULE Inner ----
VARIABLE a
RECURSIVE R(_)
R(n) == R(n)
ISpec == a = 0 /\ [][a' = a]_<<a, R(0)>>
====
