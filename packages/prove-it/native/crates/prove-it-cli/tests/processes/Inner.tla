---- MODULE Inner ----
EXTENDS Naturals
CONSTANT K
VARIABLE c
a(p) == c' = [c EXCEPT ![p] = (c[p] + K) % 3]
P(p) == a(p)
====
