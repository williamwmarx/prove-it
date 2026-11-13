---- MODULE Inner ----
EXTENDS Naturals
VARIABLE a
vars == <<a>>
IInit == a = 0
INext == a' = (a + 1) % 3
ISpec == IInit /\ [][INext]_vars /\ WF_vars(INext)
ISpec2 == IInit /\ [][INext]_<<a, vars>>
Inv == a < 2
====
