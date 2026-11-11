---- MODULE M ----
EXTENDS Naturals
CONSTANT F(_), G(_, _), C
VARIABLE x
Init == x = 0
Next == x' = F(x)
Inv == x /= 2
Inc(n) == n + 1
Add(a, b) == a + b
Zero == 0
====
