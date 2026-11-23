---- MODULE Lrnotxboxxdiaxrlast ----
VARIABLE x
Spec == LET RECURSIVE R(_)
            A(n) == ~R(n)
            Bad == [](A(x' = x))
            R(n) == <>(n)
        IN Bad
====
