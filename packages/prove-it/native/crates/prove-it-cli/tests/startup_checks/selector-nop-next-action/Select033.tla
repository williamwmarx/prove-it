(*---
description: Actual selector selected_next.
outcome: any
config: |
  INIT Init
  NEXT Next
---*)
---- MODULE Select033 ----
EXTENDS TLC,Naturals,Sequences
VARIABLES x,y
I==L::(x=0 /\ y=0)
N==L::(x'=x /\ y'=y)
Init==x=0 /\ y=0
Next==N!L
====
