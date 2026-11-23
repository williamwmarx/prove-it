---- MODULE Lrnotxboxxaxrlast ----
VARIABLE x
Spec == LET RECURSIVE R(_)
            A(n) == ~R(n)
            Bad == [](A(x' = x))
            R(n) == A(n)
        IN Bad
====
