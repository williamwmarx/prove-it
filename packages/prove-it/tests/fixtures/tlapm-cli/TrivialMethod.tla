---- MODULE TrivialMethod ----
EXTENDS Naturals, TLAPS
THEOREM ASSUME NEW P, NEW Q, P /\ Q PROVE Q /\ P
  BY ONLY Trivial
THEOREM TRUE
  BY ONLY Trivial
THEOREM 1 + 1 = 2
  BY Trivial, SMT
====
