(*---
description: Actual selector subscript_<<x,y>>_V!L.
outcome: any
config: |
  SPECIFICATION Spec
---*)
---- MODULE Select021 ----
EXTENDS TLC,Naturals,Sequences
VARIABLES x,y
V==L::<<x,y>>
Init==x=0 /\ y=0
Next==x'=1 /\ y'=y
Spec==Init /\ [][Next]_(V!L)
====
