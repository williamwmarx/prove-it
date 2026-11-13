---- MODULE Inner ----
EXTENDS Naturals
VARIABLE a
IInit == a = 0
INext == a' = (a + 1) % 3
ISpec == IInit /\ [][INext]_a
Inv == a < 3
Act == INext
====
