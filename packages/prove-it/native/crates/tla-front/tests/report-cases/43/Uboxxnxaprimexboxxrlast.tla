---- MODULE Uboxxnxaprimexboxxrlast ----
VARIABLE x
Spec == LET RECURSIVE R(_)
            A(n) == n
            R(n) == [](n)
        IN A(x' = x)
Use == [](Spec)
====
