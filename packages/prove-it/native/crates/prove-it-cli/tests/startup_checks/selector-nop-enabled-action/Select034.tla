(*---
description: Actual selector selected_enabled.
outcome: any
config: |
  INIT Init
  NEXT Next
  INVARIANT Inv
---*)
---- MODULE Select034 ----
EXTENDS TLC,Naturals,Sequences
VARIABLES x,y
I==L::(x=0 /\ y=0)
N==L::(x'=x /\ y'=y)
Init==x=0 /\ y=0
Next==x'=x /\ y'=y
Inv==ENABLED (N!L)
====
