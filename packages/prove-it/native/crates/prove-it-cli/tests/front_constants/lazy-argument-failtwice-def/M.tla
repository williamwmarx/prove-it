---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT S
VARIABLE x
Ignore(a) == TRUE
Once(a) == a = 1
Twice(a) == a + a = 2
Both(a, b) == b + a = 0
Cond(a) == IF TRUE THEN TRUE ELSE a
P1(a) == a = TRUE
P2(a) == a /\ a
RECURSIVE F(_), G(_, _)
F(n) == IF n = 0 THEN TRUE ELSE F(n - 1)
G(n, d) == IF n = 0 THEN TRUE ELSE G(n - 1, d)
C == Twice(1 \div 0)
Init == x = 0 /\ C
Next == x' = x

====
