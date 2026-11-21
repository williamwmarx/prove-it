(*---
description: Actual selector selected_init.
outcome: any
config: |
  INIT Init
  NEXT Next
---*)
---- MODULE Select032 ----
EXTENDS TLC,Naturals,Sequences
VARIABLES x,y
I==L::(x=0 /\ y=0)
N==L::(x'=x /\ y'=y)
Init==I!L
Next==x'=x /\ y'=y
====
