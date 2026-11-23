---- MODULE LetRecursiveClean ----
EXTENDS Naturals
VARIABLE x
Spec == LET RECURSIVE Sum(_)
            Twice(n) == 2 * Sum(n)
            Sum(n) == IF n = 0 THEN 0 ELSE n + Sum(n - 1)
        IN x = Twice(3)
====
