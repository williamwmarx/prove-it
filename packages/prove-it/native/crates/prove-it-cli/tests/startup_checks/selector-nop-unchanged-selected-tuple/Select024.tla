(*---
description: Actual selector unchanged_<<L::x,y>>_V!L.
outcome: any
config: |
  INIT Init
  NEXT Next
---*)
---- MODULE Select024 ----
EXTENDS TLC,Naturals,Sequences
VARIABLES x,y
V==L::<<L::x,y>>
Init==x=0 /\ y=0
Next==x'=1 /\ UNCHANGED (V!L)
====
