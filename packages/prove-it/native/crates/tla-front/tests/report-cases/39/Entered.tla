---- MODULE Entered ----
VARIABLE x
RECURSIVE R(_)
A(n) == R(n) /\ n
Bad == [](A(x' = x))
R(n) == [](A(n))
====
