---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
D1 == 1
D2 == <<x, y>>
K == x + 1
Op(a) == <<a, y>>
Wrap(a) == a
Ap(F(_)) == F(0)
f[i \in {0}] == x
J == INSTANCE Inner WITH v <- x
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(LET RECURSIVE h(_)
                    h(n) == n IN <<x, y>>)
====
