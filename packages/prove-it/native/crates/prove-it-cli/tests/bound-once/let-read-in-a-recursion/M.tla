---- MODULE M ----
EXTENDS Integers, TLC
VARIABLES x
RECURSIVE Sum(_)
Sum(n) == IF n = 0 THEN 0 ELSE n + Sum(n-1)
Twice(a) == <<a, a>>
RECURSIVE Deep(_, _)
Deep(n, a) == IF n = 0 THEN Twice(a)[2] ELSE Deep(n - 1, a)
Init == x = 0
Next == x < 20 /\ x' = x + 1 /\ LET s == Sum(x * 2) IN Twice(s)[1] >= 0 /\ Deep(x, s) >= 0
Inv == LET t == Sum(x * 3) IN Twice(t)[1] + Deep(x + 2, t) < 3000
====
