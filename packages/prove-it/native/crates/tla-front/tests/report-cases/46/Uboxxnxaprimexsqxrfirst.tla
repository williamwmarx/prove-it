---- MODULE Uboxxnxaprimexsqxrfirst ----
VARIABLE x
Spec == LET RECURSIVE R(_)
            R(n) == [](n)
            A(n) == n
        IN A(x' = x)
Use == [][Spec]_x
====
