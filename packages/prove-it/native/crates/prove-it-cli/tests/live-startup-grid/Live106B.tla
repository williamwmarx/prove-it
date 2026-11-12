---- MODULE Live106B ----
EXTENDS Naturals
VARIABLE x
RECURSIVE Sum(_)
Sum(n) == IF n = 0 THEN 0 ELSE n + Sum(n - 1)
Q == \A i \in {Sum(100) % 3} : [](x # i)
====
