---- MODULE Live107B ----
EXTENDS Naturals
VARIABLE x
RECURSIVE F(_, _)
F(n, acc) == IF n = 0 THEN acc ELSE F(n - 1, acc + acc)
Q == \A i \in {F(30, 1) % 3} : [](x # i)
====
