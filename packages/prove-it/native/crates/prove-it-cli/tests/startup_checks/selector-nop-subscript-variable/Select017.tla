(*---
description: Actual selector subscript_x_V!L.
outcome: any
config: |
  SPECIFICATION Spec
---*)
---- MODULE Select017 ----
EXTENDS TLC,Naturals,Sequences
VARIABLES x,y
V==L::x
Init==x=0 /\ y=0
Next==x'=1 /\ y'=y
Spec==Init /\ [][Next]_(V!L)
====
