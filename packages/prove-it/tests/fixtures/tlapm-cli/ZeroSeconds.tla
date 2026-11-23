---- MODULE ZeroSeconds ----
EXTENDS Naturals, TLAPS
THEOREM \A x \in Nat : x + 0 = x
  BY SMTT(0)
THEOREM \A x \in Nat : x * 1 = x
  BY SMTT(1)
====
